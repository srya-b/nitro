# KZG Vector Commitment as State Trie — Implementation Plan

## Goal

Benchmark a KZG vector commitment as a candidate replacement for the Merkle-Patricia trie, measuring TPS impact relative to an MPT baseline. The benchmark targets a **payments-only chain** — EOA accounts only, pure value transfers, no contracts, no ArbOS — to isolate the cost of the account-state commitment scheme without contamination from contract execution or storage-MPT overhead.

## Architectural picture

Geth's `state.Trie` interface (in `go-ethereum/core/state/database.go:79-161`) is the seam where the Merkle-Patricia trie meets the StateDB. The codebase already supports an alternative implementation (verkle, `trie/verkle.go:49-73`) selected at runtime via a `triedb.Config` flag. We add a third option (KZG) by exactly the same pattern: a `KZGTrie` struct that wraps our KZG commitment library and satisfies the same 15-method interface, plus a new `IsKZG` config flag, plus a branch in `Database.OpenTrie` (`core/state/database.go:262-289`).

Because the workload is payments-only, the storage and code paths in StateDB are dormant. KZGTrie returns constants for storage-root and code-hash fields; all storage operations are noops; contract execution is bypassed by a custom block producer on the Nitro side.

---

## Locked-in design parameters

- **Commitment scheme**: KZG over BLS12-381, **evaluation form (Lagrange basis)**. Single-slot updates are O(1) (one scalar-mult against the relevant basis point + one point-add). Batch updates of k slots are one MSM of size k.
- **State model**: two parallel vectors `balances[N]` and `nonces[N]` indexed by an account index `i ∈ [0, N)`. No storage, no code, no other per-account fields committed.
- **Account → index map**: bucketed cuckoo hash table, in-consensus, committed via **two separate KZG vectors** `C_T1` and `C_T2` (one per cuckoo lane) — split-lane design.
- **Cuckoo parameters**:
  - 2 lanes (d=2), bucket size B=8, no stash, MAX_KICKS=500
  - Two SipHash-128 hash functions with constants fixed at genesis
  - Deterministic 2× grow + canonical reinsert on overflow (essentially never fires at the resulting ≤50% effective load)
- **Initial capacity N**: 2²⁵ (≈33M account slots). Lagrange basis at this size ≈ 1.5 GB compressed BLS12-381 G1.
- **Total commitments per state**: four — `C_balances`, `C_nonces`, `C_T1`, `C_T2`. All length N, sharing one Lagrange basis.
- **State root encoding**:
  ```
  state_root = Keccak256(
      C_balances || C_nonces || C_T1 || C_T2
      || u64_be(next_index)
      || u64_be(N)
  )
  ```
  32 bytes in the block header's `Root` field. Full 48-byte commitments persisted under `K:com:<root>` in ethdb.
- **Account index allocation**: monotonic counter (`next_index`), no reuse. Documented limitation (see below); future work to add free-list.
- **Storage / contracts**: not supported. No EVM execution. No ArbOS. No per-account storage trie ever opened. `StateAccount.Root` and `StateAccount.CodeHash` filled with constants (`emptyRoot`, `emptyCodeHash`) on every account read.
- **Library**: KZG primitives written **from scratch** on top of geth's pinned `gnark-crypto`. The code at `/home/admin/b-epsilon-kv` serves as a reference for the four operations (commit, update slot, batch update, basis load), not as a dependency.

---

## Defaults baked in — override during review if any are wrong

| Item | Default | Where to change |
|---|---|---|
| Cuckoo hash functions | SipHash-128 with two fixed key pairs | constants in `trie/kzg/cuckoo.go` |
| SRS source | Fake Lagrange basis with known τ; env var `KZG_SRS_PATH` to load real basis | startup wiring in `trie/kzg/setup.go` |
| Tx format | Reuse legacy Ethereum tx (signature gives `from`; fields used: `to`, `value`, `nonce`; gas and data ignored) | block producer in `execution/payments/` |
| Fee per tx | Zero | block producer; switch to fixed-fee constant if desired |
| Fee recipient | Fixed validator address from genesis (unused if fee = 0) | genesis config |
| Validation | Sufficient balance + matching nonce + valid signature; rejected pre-application if any fails | block producer |
| Genesis | JSON file of (address, balance) pairs; inserted into cuckoo and committed at chain init | `execution/payments/genesis.go` |
| Curve | BLS12-381 | hard pin in `trie/kzg/internal/kzg.go` |
| Lagrange basis residency | All in-memory at process start | future: memory-map at very large N |

---

## Persistence: ethdb keyspace

```
K:bal:<u64 be index>           → 32-byte balance (fr.Element)
K:non:<u64 be index>           → 32-byte nonce (fr.Element, low 8 bytes used)
K:ckk1:<u64 be cell index>     → cuckoo lane T1 cell (fr.Element, packed)
K:ckk2:<u64 be cell index>     → cuckoo lane T2 cell (fr.Element, packed)
K:com:<32-byte root>           → C_bal || C_non || C_T1 || C_T2 (4 × 48 bytes compressed)
K:meta:nextindex               → u64 BE
K:meta:cap                     → u64 BE (N)
```

Cuckoo cell encoding (one `fr.Element`):
```
bits [253..193]  reserved (zero)
bit  [192]       occupied flag (1 = occupied, 0 = empty)
bits [191..32]   address (160 bits)
bits [31..0]     account_index (32 bits)
```

Empty cell = the zero field element (occupied flag = 0). Initial state is the all-zeros vector with commitment = identity.

Lagrange basis loaded from `KZG_SRS_PATH` or generated at startup with `FastFakeLagrangeBasis(N)`. Held in memory for the process lifetime.

---

## state.Trie interface implementation

```
GetAccount(addr)           → cuckoo lookup → return (balances[i], nonces[i], emptyRoot, emptyCodeHash)
GetStorage(addr, key)      → return nil, nil  (no storage)
UpdateAccount(addr, acct)  → if new addr: cuckoo insert + allocate next_index;
                              queue balance/nonce delta against C_balances, C_nonces
UpdateStorage              → noop
DeleteAccount(addr)        → mark cuckoo cell empty (zero); zero balance/nonce vector slots
DeleteStorage              → noop
UpdateContractCode         → noop
Hash()                     → compute current Keccak preimage
Commit(collectLeaf)        → flush pending deltas: 4 MSMs, write batch to ethdb, return new root
GetKey, PrefetchAccount, PrefetchStorage, NodeIterator, Prove, Witness → stubs (panic / nil / noop)
```

---

## Per-block commit lifecycle

1. Block producer collects validated transfers.
2. For each tx, apply through StateDB (sender balance↓, recipient balance↑, sender nonce++, recipient created if new).
3. StateDB queues changes in its journal as usual (only balance/nonce changes get journaled — no storage, no code).
4. At commit, `KZGTrie.Commit(true)` walks the journal:
   - Compute delta for each changed balance/nonce slot.
   - For each new account: cuckoo insert (may trigger kick chain across cells in T1/T2).
   - Build delta maps for all four vectors.
   - Apply: four MSMs (one per commitment), each of size equal to the changes for that commitment.
   - Update root = `Keccak256(C_bal || C_non || C_T1 || C_T2 || meta)`.
   - Write all dirty cells + new commitments to ethdb via batch.
5. Block header carries the 32-byte root.

---

## Phased implementation

### P0 — Compile-clean skeleton (1-2 days)

- New `go-ethereum/trie/kzg/` package with `KZGTrie` struct; all 15 `state.Trie` methods returning sensible zeros / panics.
- `triedb.Config.IsKZG` plumbed; `KZGDefaults` config.
- Branch in `core/state/database.go:OpenTrie` selecting KZGTrie when `IsKZG` is set.
- Geth + Nitro build clean; existing tests still pass.
- KZGTrie is constructible but does nothing useful yet.

**Acceptance**: `go build ./...` is clean from both `go-ethereum/` and Nitro root; existing geth state tests still pass with `IsKZG=false`.

### P1 — KZG primitives + commitment lifecycle (~1 week)

- Implement `trie/kzg/internal/kzg.go` from scratch (~150 LOC) on top of geth's pinned gnark-crypto:
  ```go
  type Setup struct { Lagrange []bls12381.G1Affine }
  func LoadSetup(path string, N int) (*Setup, error)
  func FastFakeLagrangeBasis(N int) *Setup
  func (s *Setup) Commit(values []fr.Element) bls12381.G1Affine
  func (s *Setup) UpdateSlot(c G1Affine, idx int, old, new fr.Element) G1Affine
  func (s *Setup) BatchUpdate(c G1Affine, deltas map[int]fr.Element) G1Affine
  ```
- SRS path via env var with `FastFakeLagrangeBasis` fallback.
- Implement persistence: write cells + commitments via ethdb `Batch`.
- Implement `Hash()` returning current root preimage hash.
- Implement `Commit()` end-to-end: gather deltas, run MSMs, write batch, return root.
- Unit tests: insert N accounts, commit, restart-load, verify root matches deterministic recompute.

### P2 — Cuckoo index map (~3-5 days)

- Bucketed cuckoo (B=8), two SipHash-128 lanes with fixed keys.
- Persist cuckoo cells to ethdb under `K:ckk1:` / `K:ckk2:`.
- Wire `GetAccount` → cuckoo lookup → balance/nonce vector reads.
- New-account path: allocate `next_index`, insert into cuckoo, fan out updates to all four commitments.
- Deterministic 2× grow on overflow with rehash-event logging (rare).
- **No tx-revert journal** — payments are validated upfront and rejected if invalid, never applied-then-reverted. Eliminates the need to record kick chains for replay-on-revert.

### P3 — Payments-only block producer (~1 week)

Custom block producer in `nitro/execution/payments/` that bypasses ArbOS:

- Reads transfers from a queue (initially a simple in-memory generator; later configurable from a file).
- Validates each: sufficient balance, matching nonce, valid ecrecover signature.
- Applies via direct StateDB calls: `SubBalance(from, value)`, `AddBalance(to, value)`, `SetNonce(from, nonce+1)`.
- Writes block with state root from `KZGTrie.Commit`.
- New chain config flag `IsPaymentsOnly bool` to gate this mode. Set together with `IsKZG` for the experimental chain; baseline runs `IsPaymentsOnly=true, IsKZG=false`.
- Genesis: load JSON (address, balance) pairs; insert each into cuckoo and compute initial commitments.

### P4 — Recovery on restart (~2 days)

- On open: read latest root from head block header.
- Load commitments from `K:com:<root>`.
- Validate vector / cuckoo cells reachable via direct key lookup.
- Smoke test: produce N blocks → restart → produce another N → verify deterministic recompute.

### P5 — Benchmark harness (~1 week)

Synthetic workload generator: uniform random (from, to) pairs; optionally Zipf for skewed access patterns.

Two configurations from the same binary:
- **Baseline**: payments-only block producer + vanilla MPT account trie.
- **Experiment**: payments-only block producer + KZG account trie.

Metrics:
- Sustained TPS over a configurable window (10s, 60s, 600s)
- Per-block commit latency (broken into delta-gather, MSM, batch-write phases)
- Per-block disk write volume
- Rehash event count (should be zero under normal workload)
- Memory residency of Lagrange basis

Instrument `StateDB.Commit` to surface phase timings.

**Total estimated effort**: ~5-6 weeks of focused work for a single engineer, from skeleton to first benchmark numbers.

---

## Known limitations and future work

- **`next_index` is monotonic; deleted accounts burn their slot permanently.** Max-ever-allocated accounts is capped at N (not max-live). Acceptable for benchmarks. *To remove*: add a committed free-list (small extra vector with its own KZG commitment, or appended slots on `C_balances`) and modify the allocator in `trie/kzg/cuckoo.go` to pop from the free-list before incrementing the counter.

- **No stash.** B=8 split-lane at ≤50% effective load makes kick chains short and rehash essentially nonexistent. If real workloads expose tail-latency issues from rehash events, add a stash as a separate small KZG commitment (e.g., 32 cells, separate small Lagrange basis subset) or appended slots on one lane. *Decision was made to drop the stash here for simplicity at the design stage; this is the documented reversal path.*

- **No contract execution / no storage / no ArbOS.** Pure value transfers only. *To re-enable*: restore storage MPT (per-account storage tries), restore ArbOS, decide whether to add `Root` and `CodeHash` to the commitment or keep them in an uncommitted ethdb side-table keyed by `account_index`. Re-enabling contracts also implies restoring StateDB's tx-revert journal machinery and adding a `cuckooInsert` journal entry that records the full kick chain for replay-on-revert.

- **No tx reverts.** Validation happens upfront; invalid txs are rejected without state modification. Adequate for value-transfer semantics; would need restoration if contracts are added.

- **Capacity N is fixed at chain init.** Growing N during operation requires rebuilding all four commitments over a 2×-larger Lagrange basis. Not implemented in the benchmark; pre-size N at chain init to a value that comfortably exceeds expected accounts.

- **Trusted setup is fake by default.** Benchmarks use `FastFakeLagrangeBasis` with known τ. Real deployment would need a real ceremony or a converted Powers-of-Tau SRS. Mostly relevant if numbers are ever extrapolated to a deployment context.

- **Header `Root` is Keccak of commitments**, not the commitments themselves (which are 4×48 = 192 bytes, too large for the 32-byte header field). Block validation must read the digest, load the full commitments from `K:com:<root>`, and verify against the expected vectors.

---

## Risk register

| Risk | Mitigation |
|---|---|
| Lagrange basis memory pressure at large N | Cap N at chain init; document basis RAM cost; consider memory-mapping the basis file for very large N |
| StateDB code paths assume storage methods do real work | All storage methods explicitly noop; smoke tests in P1 verify pass-through |
| Tx signature verification cost dominates KZG cost | Use ecrecover (already in geth); measure separately in P5; consider BLS aggregate signatures in future work |
| Cuckoo rehash spike in production | At ≤50% load, expected once per ~2^40 inserts; log every event; not a problem for the benchmark window |
| Determinism across machines (SipHash, fr.Element encoding) | Pin gnark-crypto version; SipHash with explicit keys; unit test root recomputation on different platforms in P1 |
| `gnark-crypto` version differences across modules | Pin one version (likely match geth's `v0.18.x`); verify gnark-crypto API for KZG / MSM / curve is unchanged across the pinned span; resolve in P0 |

---

## Decisions made during planning (rationale archive)

For future reference / when this plan is revisited:

- **Split-lane cuckoo (two commitments)** over one combined vector — capacity. For a fixed Lagrange basis of size L, the combined design caps accounts at 0.95·L (cuckoo-limited); split-lane caps at L (balances-limited) and runs the cuckoo at 50% load with vastly shorter kick chains.

- **Bucketed cuckoo with B=8** — sustainable load jumps from ~50% (B=1) to ~98% (B=8); expected kick chain at high load drops from ~50+ to ~2.

- **Account index separate from cuckoo cell position** — a kick chain that moves an entry across cuckoo positions must NOT change which `balances[i]` slot the account points to. Account index is allocated once and stored *in* the cuckoo cell along with the address.

- **Evaluation form (Lagrange basis) not coefficient form** — vector entries are direct values, single-slot update is O(1) via the i-th Lagrange basis G1 point. Coefficient form would require IFFT per update and the semantics don't match state.

- **KZG primitives written from scratch** rather than vendored from b-epsilon-kv — the library is entangled with its own state model (LRU cache, Pebble keys, payment engine); we need ~150 LOC of clean primitives, not the whole package. b-epsilon-kv serves as a correctness reference.

- **No contract execution** — simplifies measurement, avoids ArbOS storage overhead, eliminates need for revert journal in cuckoo kick chains. Documented as future work to re-enable.

- **`next_index` committed in state root preimage, monotonic, no free-list** — simplest deterministic allocation; documented as a known limitation for future iteration.

- **No stash on the cuckoo** — at 50% effective load with B=8, stash use is vanishingly rare; rehash is the fallback. Documented reversal path if real workloads expose problems.

- **Hybrid-MPT storage was considered and rejected** — the cleaner measurement is pure payments-only, achieved by bypassing ArbOS in P3. The cost is one extra implementation phase; the gain is uncontaminated TPS numbers.
