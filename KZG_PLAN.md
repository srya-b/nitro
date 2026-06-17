# KZG Vector Commitment as State Trie — Implementation Plan

## Goal

Benchmark a KZG vector commitment as a candidate replacement for the Merkle-Patricia trie, measuring TPS impact relative to an MPT baseline. The benchmark targets a **payments-only chain** — EOA accounts only, pure value transfers, no contracts, no ArbOS — to isolate the cost of the account-state commitment scheme without contamination from contract execution or storage-MPT overhead.

## How this document is structured

This file is the **architecture / design doc**. It captures the locked-in decisions, the why behind them, and the high-level shape of each phase. Read once at the start of the project, refer back when revisiting a decision.

The actual implementation is driven from a set of per-phase **implementation specs** under `nitro/docs/kzg-impl/`:

```
nitro/docs/kzg-impl/
  README.md            — orientation, phase dependency map
  P0_skeleton.md       — stub KZGTrie + OpenTrie switch
  P1_kzg_primitives.md — KZG library from scratch + commitment lifecycle
  P2_cuckoo.md         — bucketed cuckoo index map
  P3_payments_block.md — payments-only block producer
  P4_recovery.md       — restart / recovery
  P5_benchmark.md      — benchmark harness + parameter sweep
```

Each per-phase spec is self-contained: exact file paths, function signatures, step-by-step pseudocode for non-trivial algorithms, concrete test cases (input → expected output), and self-checkable acceptance criteria. A downstream implementer (cheap-model or human) needs that phase's spec + this design doc as background — not the other phase specs. Phases reference each other only at their interfaces (types and functions one produces and the next consumes).

If a phase spec doesn't answer an implementation question, the spec is wrong — update the spec, don't improvise in code.

---

## Architectural picture

Geth's `state.Trie` interface (in `go-ethereum/core/state/database.go:79-161`) is the seam where the Merkle-Patricia trie meets the StateDB. The codebase already supports an alternative implementation (verkle, `trie/verkle.go:49-73`) selected at runtime via a `triedb.Config` flag. We add a third option (KZG) by exactly the same pattern: a `KZGTrie` struct that wraps our KZG commitment library and satisfies the same 15-method interface, plus a new `IsKZG` config flag, plus a branch in `Database.OpenTrie` (`core/state/database.go:262-289`).

Because the workload is payments-only, the storage and code paths in StateDB are dormant. KZGTrie returns constants for storage-root and code-hash fields; all storage operations are noops; contract execution is bypassed by a custom block producer on the Nitro side.

---

## Locked-in design parameters

- **Commitment scheme**: KZG over BN254, **evaluation form (Lagrange basis)**. Single-slot updates are O(1) (one scalar-mult against the relevant basis point + one point-add). Batch updates of k slots are one MSM of size k.
- **State model**: two parallel vectors `balances[N]` and `nonces[N]` indexed by an account index `i ∈ [0, N)`. No storage, no code, no other per-account fields committed.
- **Account → index map**: bucketed cuckoo hash table, in-consensus, committed via **two separate KZG vectors** `C_T1` and `C_T2` (one per cuckoo lane) — split-lane design.
- **Cuckoo parameters**:
  - 2 lanes (d=2), bucket size B=8, no stash, MAX_KICKS=500
  - **Hash functions h₁ and h₂ derived from one `Keccak256(addr)` call, slicing two disjoint 4-byte ranges of the output** (see Hash function for the cuckoo below for trade-offs and alternatives)
  - Deterministic 2× grow + canonical reinsert on overflow (essentially never fires at the resulting ≤50% effective load)
- **Initial capacity N**: 2²⁵ (≈33M account slots). Lagrange basis at this size ≈ 1 GB compressed BN254 G1 (32 bytes/point vs 48 bytes for BLS12-381).
- **Total commitments per state**: four — `C_balances`, `C_nonces`, `C_T1`, `C_T2`. All length N, sharing one Lagrange basis.
- **State root encoding**:
  ```
  state_root = Keccak256(
      C_balances || C_nonces || C_T1 || C_T2
      || u64_be(next_index)
      || u64_be(N)
  )
  ```
  32 bytes in the block header's `Root` field. Full 32-byte commitments persisted under `K:com:<root>` in ethdb.
- **Account index allocation**: monotonic counter (`next_index`), no reuse. Documented limitation (see below); future work to add free-list.
- **Storage / contracts**: not supported. No EVM execution. No ArbOS. No per-account storage trie ever opened. `StateAccount.Root` and `StateAccount.CodeHash` filled with constants (`emptyRoot`, `emptyCodeHash`) on every account read.
- **Library**: KZG primitives written **from scratch** on top of geth's pinned `gnark-crypto`. The code at `/home/admin/b-epsilon-kv` serves as a reference for the four operations (commit, update slot, batch update, basis load), not as a dependency.

---

## Defaults baked in — override during review if any are wrong

| Item | Default | Where to change |
|---|---|---|
| Cuckoo hash functions | `Keccak256(addr)`, slice bytes `[0:4]` for h₁ and `[16:20]` for h₂ | helper in `trie/kzg/cuckoo.go`; swap to a faster mixer here if P5 shows it's a bottleneck |
| SRS source | Fake Lagrange basis with known τ; env var `KZG_SRS_PATH` to load real basis | startup wiring in `trie/kzg/setup.go` |
| Tx format | Reuse legacy Ethereum tx (signature gives `from`; fields used: `to`, `value`, `nonce`; gas and data ignored) | block producer in `execution/payments/` |
| Fee per tx | Zero | block producer; switch to fixed-fee constant if desired |
| Fee recipient | Fixed validator address from genesis (unused if fee = 0) | genesis config |
| Validation | Sufficient balance + matching nonce + valid signature; rejected pre-application if any fails | block producer |
| Genesis | JSON file of (address, balance) pairs; inserted into cuckoo and committed at chain init | `execution/payments/genesis.go` |
| Curve | BN254 | hard pin in `trie/kzg/internal/kzg.go` |
| Lagrange basis residency | All in-memory at process start | future: memory-map at very large N |

---

## Persistence: ethdb keyspace

```
K:bal:<u64 be index>           → 32-byte balance (fr.Element)
K:non:<u64 be index>           → 32-byte nonce (fr.Element, low 8 bytes used)
K:ckk1:<u64 be cell index>     → cuckoo lane T1 cell (fr.Element, packed)
K:ckk2:<u64 be cell index>     → cuckoo lane T2 cell (fr.Element, packed)
K:com:<32-byte root>           → C_bal || C_non || C_T1 || C_T2 (4 × 32 bytes compressed)
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

Lagrange basis loaded from `KZG_SRS_PATH` or generated at startup with `FastFakeLagrangeBasis(N)`. Held in memory for the process lifetime (see Memory model below for handling at very large N).

---

## Hash function for the cuckoo

The two cuckoo hash functions h₁, h₂ are derived from a single Keccak256 over the address:

```go
hash := crypto.Keccak256(addr.Bytes())            // already in geth
h1   := binary.BigEndian.Uint32(hash[0:4]) % m
h2   := binary.BigEndian.Uint32(hash[16:20]) % m
```

Keccak's avalanche makes distant output bytes statistically independent, so slicing one digest gives two effectively-independent hash functions without paying for two hash calls.

### Why not a faster hash (SipHash etc.)

SipHash-128 is the standard pick for in-memory hash tables (Rust HashMap, Python dict, Go runtime map). The reason — keyed-PRF security against algorithmic-complexity attacks — relies on the key being **secret**, randomized per process. In our setting the key has to be **fixed at genesis and identical across all nodes**, so it's public. With a public key, SipHash provides good mixing but no PRF advantage over any other well-mixing hash.

Adversarial security against grinding attacks is bounded by the cost of generating Ethereum keypairs (~10 µs each for secp256k1 + Keccak256 of the pubkey to derive the address). That cost dominates whatever we add on top — the hash function we apply to the address contributes essentially nothing to grinding cost.

So the relevant trade-off is **speed vs. dependency simplicity**, not security.

### Trade-offs vs. alternatives — for future revisiting

| Option | Per-hash cost | New dependency? | Notes |
|---|---|---|---|
| **Keccak256(addr), slice — current choice** | ~1 µs | No, already in geth | Cryptographic mixing, no constants to specify, one line of code |
| **SipHash-128 with two fixed keys** | ~100 ns | Yes — vendor `github.com/dchest/siphash` or equivalent | Two 128-bit constants must be specified at genesis; ~10× faster than Keccak; the "PRF" rationale is voided by public key, but mixing is still good |
| **Blake3 (truncate or sub-hash)** | ~150 ns | Yes — `github.com/zeebo/blake3` or equivalent | Modern fast cryptographic hash; arguably the cleanest "fast + safe" alternative if Keccak proves too slow; well-distributed even when truncated |
| **xxHash3** | ~50 ns | Yes — `github.com/cespare/xxhash/v2` | Very fast, non-cryptographic; same caveats as SipHash with public key but even faster; well-tested in Go ecosystem |
| **HighwayHash** | ~80 ns | Yes — Google's library | Similar to SipHash-128 with better SIMD throughput; less common in Go |
| **Raw address slicing (no hash)** | ~0 | No | **Not viable** — vanity-grinded addresses (0xdead..., 0x000...) cluster catastrophically in h₁ |

**Cost at 100k TPS**: ~2 hashes per tx × 2 lookups (sender + recipient) ≈ 400k hashes/sec.
- Keccak: ~400 ms of CPU per second (~40% of one core) — measurable but likely dwarfed by MSM and batch-write costs.
- SipHash / Blake3 / xxHash3: ~20-60 ms/sec (~2-6% of one core).

**When to swap**: if P5 profiling shows the cuckoo hash is a top-3 CPU cost in `Commit` or in tx-lookup, swap in this order of preference:
1. **Blake3** — fast and cryptographic, clean replacement
2. **SipHash-128** — fastest with reasonable mixing, vendoring is small
3. **xxHash3** — fastest, only if security against grinding doesn't matter for the experiment

The swap is localized to the helper in `trie/kzg/cuckoo.go`; nothing else depends on the choice. If swapping, also update genesis spec and rationale doc to record the chosen constants.

### Domain separation

We use slicing rather than two domain-separated Keccak calls (`Keccak("h1" || addr)` and `Keccak("h2" || addr)`). Slicing is sufficient because Keccak's diffusion makes distant output bytes independent in practice. Belt-and-suspenders would be 2× the hash cost for negligible safety gain.

---

## Memory model

The design is **disk-backed for state**. State vectors and the cuckoo table are not held in RAM — every cell read is a single KV get against ethdb. There is no expectation that the full state fits in memory.

### What lives in RAM

- **Lagrange basis**: N G1Affine points. At N=2²⁵ this is ~1 GB compressed (BN254 G1 is 32 bytes compressed). Required for fast MSM (each term is `delta_i · basis[i]`, so `basis[i]` must be addressable).
- **Current commitments**: four G1Affine points ≈ 200 bytes total.
- **Per-block delta buffer during commit**: a `map[index→fr.Element]` per commitment, sized to slots actually changed in the current block (bounded by block transaction count — thousands at most). Cleared after commit.
- **`next_index`, `capacity_N`**: a few u64s.
- **Pebble block cache** (configurable; see below). We do not write any application-level cache on top of ethdb cells — that's Pebble's job.

### What lives on disk (ethdb), read on demand

- Every balance cell (`K:bal:<index>`), nonce cell (`K:non:<index>`), and cuckoo cell (`K:ckk1:`, `K:ckk2:`).
- Historical commitments by root (`K:com:<root>`).
- All metadata (`K:meta:`).

### ethdb cache: what stays warm in RAM

State residency is determined by Pebble's internal block cache, not by application logic. We delegate caching entirely to the DB layer.

- **Cache type**: Pebble block cache, configured via `pebble.Options.Cache` when opening the DB (already wired in geth's `ethdb/pebble`).
- **Default size for benchmark runs**: 2 GB, exposed as a CLI flag. State on disk at N=2²⁵ is roughly:
  - balances vector: 32 B × 2²⁵ ≈ 1 GB
  - nonces vector: 32 B × 2²⁵ ≈ 1 GB
  - cuckoo cells (2 lanes × N × 32 B): ≈ 2 GB
  - commitments + metadata: negligible
  - **Total ≈ 4 GB.** A 2 GB cache covers a typical hot working set; sweep this in P5 to characterize cold-vs-warm behavior.
  - Note: Lagrange basis RAM drops from ~1.5 GB (BLS12-381) to ~1 GB (BN254) due to the smaller compressed G1 size.
- **Eviction policy**: Pebble's segmented LRU on SST blocks. Pages get pulled in on read, evicted under memory pressure. No application code involved.
- **Why no custom LRU**: avoids double-caching, avoids cache-invalidation bugs, and keeps the implementation small. The DB layer already does this well; our job is to size it correctly.
- **Surface**: configurable via a Nitro CLI flag passed through to the underlying `ethdb` open path. P5 sweeps this parameter alongside N and workload.

### I/O per operation

- **GetAccount**: 1-2 KV range scans (one per cuckoo lane, B=8 contiguous cells each — Pebble returns the whole bucket in a single scan). If found, 2 additional KV gets for the balance and nonce slots. If absent, returns zero account with no further reads.
- **Cuckoo insert (new account)**: range scan of bucket h₁(A); if full, range scan of the kicked entry's alternate bucket; repeat. Expected kick chain at 50% load ≈ 2 cells → ≈ 2-3 range scans total. Bounded by `MAX_KICKS=500` even pathologically.
- **Commit**: one ethdb `Batch` containing all changed balance cells, nonce cells, cuckoo cells, the four new commitments, and metadata. Written and synced atomically.

### Lagrange basis at large N

- **N ≤ 2²⁵ (~1.5 GB)**: fits comfortably in RAM on any modern machine. No special handling.
- **N ≥ 2²⁶**: memory-map the basis file from disk. MSM access pattern is random across changed indices, but the per-block working set is small (thousands of hot indices); the OS page cache handles it. Optionally `mlock` hot pages or maintain an LRU on basis indices if profiling shows page-fault overhead during commit.
- **Future option**: chunked lazy load with explicit caching — only worth the engineering if mmap proves insufficient.

### Genesis bootstrap with very large initial allocations

- For small genesis (< ~1M accounts): build each commitment with a single MSM over all initial values — needs values in RAM for the MSM duration, then they go to disk.
- For very large genesis: build incrementally via `UpdateSlot` per entry, O(1) RAM at the cost of N scalar-multiplications instead of one N-MSM. Slower setup, no memory pressure.

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

### P0 — Compile-clean skeleton

- New `go-ethereum/trie/kzg/` package with `KZGTrie` struct; all 15 `state.Trie` methods returning sensible zeros / panics.
- `triedb.Config.IsKZG` plumbed; `KZGDefaults` config.
- Branch in `core/state/database.go:OpenTrie` selecting KZGTrie when `IsKZG` is set.
- Geth + Nitro build clean; existing tests still pass.
- KZGTrie is constructible but does nothing useful yet.

**Acceptance**: `go build ./...` is clean from both `go-ethereum/` and Nitro root; existing geth state tests still pass with `IsKZG=false`.

### P1 — KZG primitives + commitment lifecycle

- Implement `trie/kzg/internal/kzg.go` from scratch (~150 LOC) on top of geth's pinned gnark-crypto:
  ```go
  type Setup struct { Lagrange []bn254.G1Affine }
  func LoadSetup(path string, N int) (*Setup, error)
  func FastFakeLagrangeBasis(N int) *Setup
  func (s *Setup) Commit(values []fr.Element) bn254.G1Affine
  func (s *Setup) UpdateSlot(c G1Affine, idx int, old, new fr.Element) G1Affine
  func (s *Setup) BatchUpdate(c G1Affine, deltas map[int]fr.Element) G1Affine
  ```
- SRS path via env var with `FastFakeLagrangeBasis` fallback.
- Implement persistence: write cells + commitments via ethdb `Batch`.
- Implement `Hash()` returning current root preimage hash.
- Implement `Commit()` end-to-end: gather deltas, run MSMs, write batch, return root.
- Unit tests: insert N accounts, commit, restart-load, verify root matches deterministic recompute.

### P2 — Cuckoo index map

- Bucketed cuckoo (B=8) with h₁, h₂ derived from `Keccak256(addr)` slicing (see Hash function for the cuckoo).
- Persist cuckoo cells to ethdb under `K:ckk1:` / `K:ckk2:`.
- Wire `GetAccount` → cuckoo lookup → balance/nonce vector reads.
- New-account path: allocate `next_index`, insert into cuckoo, fan out updates to all four commitments.
- Deterministic 2× grow on overflow with rehash-event logging (rare).
- **No tx-revert journal** — payments are validated upfront and rejected if invalid, never applied-then-reverted. Eliminates the need to record kick chains for replay-on-revert.

### P3 — Payments-only block producer

Custom block producer in `nitro/execution/payments/` that bypasses ArbOS:

- Reads transfers from a queue (initially a simple in-memory generator; later configurable from a file).
- Validates each: sufficient balance, matching nonce, valid ecrecover signature.
- Applies via direct StateDB calls: `SubBalance(from, value)`, `AddBalance(to, value)`, `SetNonce(from, nonce+1)`.
- Writes block with state root from `KZGTrie.Commit`.
- New chain config flag `IsPaymentsOnly bool` to gate this mode. Set together with `IsKZG` for the experimental chain; baseline runs `IsPaymentsOnly=true, IsKZG=false`.
- Genesis: load JSON (address, balance) pairs; insert each into cuckoo and build initial commitments. For small genesis use one MSM per commitment; for very large genesis use incremental `UpdateSlot` per entry (constant RAM — see Memory model).

### P4 — Recovery on restart

- On open: read latest root from head block header.
- Load commitments from `K:com:<root>`.
- Validate vector / cuckoo cells reachable via direct key lookup.
- Smoke test: produce N blocks → restart → produce another N → verify deterministic recompute.

### P5 — Benchmark harness

Synthetic workload generator: uniform random (from, to) pairs; optionally Zipf for skewed access patterns.

Two configurations from the same binary:
- **Baseline**: payments-only block producer + vanilla MPT account trie.
- **Experiment**: payments-only block producer + KZG account trie.

Metrics:
- Sustained TPS over a configurable window (10s, 60s, 600s)
- Per-block commit latency (broken into delta-gather, MSM, batch-write phases)
- Per-block disk write volume
- Rehash event count (should be zero under normal workload)
- Lagrange basis residency (process RSS attributable to the basis)
- Pebble cache hit rate (DB-reported) at each configured cache size

Parameter sweeps:
- N ∈ {2²⁰, 2²², 2²⁴, 2²⁵, 2²⁶}
- Pebble cache size ∈ {256 MB, 1 GB, 4 GB, 16 GB} — characterize cold-vs-warm regimes
- Workload access pattern: uniform vs Zipf (skew parameter swept)

Instrument `StateDB.Commit` to surface phase timings.

---

## Known limitations and future work

- **`next_index` is monotonic; deleted accounts burn their slot permanently.** Max-ever-allocated accounts is capped at N (not max-live). Acceptable for benchmarks. *To remove*: add a committed free-list (small extra vector with its own KZG commitment, or appended slots on `C_balances`) and modify the allocator in `trie/kzg/cuckoo.go` to pop from the free-list before incrementing the counter.

- **No stash.** B=8 split-lane at ≤50% effective load makes kick chains short and rehash essentially nonexistent. If real workloads expose tail-latency issues from rehash events, add a stash as a separate small KZG commitment (e.g., 32 cells, separate small Lagrange basis subset) or appended slots on one lane. *Decision was made to drop the stash here for simplicity at the design stage; this is the documented reversal path.*

- **No contract execution / no storage / no ArbOS.** Pure value transfers only. *To re-enable*: restore storage MPT (per-account storage tries), restore ArbOS, decide whether to add `Root` and `CodeHash` to the commitment or keep them in an uncommitted ethdb side-table keyed by `account_index`. Re-enabling contracts also implies restoring StateDB's tx-revert journal machinery and adding a `cuckooInsert` journal entry that records the full kick chain for replay-on-revert.

- **No tx reverts.** Validation happens upfront; invalid txs are rejected without state modification. Adequate for value-transfer semantics; would need restoration if contracts are added.

- **Capacity N is fixed at chain init.** Growing N during operation requires rebuilding all four commitments over a 2×-larger Lagrange basis. Not implemented in the benchmark; pre-size N at chain init to a value that comfortably exceeds expected accounts.

- **Trusted setup is fake by default.** Benchmarks use `FastFakeLagrangeBasis` with known τ. Real deployment would need a real ceremony or a converted Powers-of-Tau SRS. Mostly relevant if numbers are ever extrapolated to a deployment context.

- **Header `Root` is Keccak of commitments**, not the commitments themselves (which are 4×32 = 128 bytes, too large for the 32-byte header field). Block validation must read the digest, load the full commitments from `K:com:<root>`, and verify against the expected vectors.

---

## Risk register

| Risk | Mitigation |
|---|---|
| Lagrange basis memory pressure at large N | Cap N at chain init; document basis RAM cost; mmap the basis file for N ≥ 2²⁶ (see Memory model section) |
| Per-block KV read latency dominates commit at high TPS | Size Pebble's block cache to cover the working set (default 2 GB; configurable). No application-level cache — DB handles it. Sweep cache size in P5 to find the knee. |
| Cuckoo hash function CPU cost becomes a bottleneck | Default is Keccak256-slice (~1 µs/hash). If P5 profiling shows it's a top-3 cost, swap to Blake3 (~150 ns) or SipHash-128 (~100 ns) — localized change in `trie/kzg/cuckoo.go`. See "Hash function for the cuckoo" for the trade-off table. |
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

- **BN254 over BLS12-381** — three reasons: (1) BN254 has faster finite-field arithmetic due to its smaller 254-bit prime, which directly reduces MSM and scalar-multiplication cost in the commitment/proof path; (2) Ethereum's EIP-196/197 precompiles natively support BN254, making any future on-chain verification cheaper; (3) the PSE Perpetual Powers of Tau ceremony (`github.com/privacy-ethereum/perpetualpowersoftau`) is on BN254, providing a real, widely-audited SRS to replace `FastFakeLagrangeBasis` without running a new ceremony. The tradeoff is that BN254 offers ~100-bit security vs ~128-bit for BLS12-381, but this is acceptable for a benchmark-focused chain.
- **Keccak256(addr) over SipHash-128 for the cuckoo hash functions** — SipHash's PRF-with-secret-key advantage is voided when the key has to be public for consensus, leaving only "fast mixing" as its benefit. Keccak is already in geth (no new dependency), needs no constants in the genesis spec, and the hash-function CPU cost is unlikely to dominate (MSM and batch writes likely heavier). If profiling later shows hashing is a real bottleneck, swap to Blake3 or SipHash-128 — change is localized to `trie/kzg/cuckoo.go`. Full trade-off table preserved in the "Hash function for the cuckoo" section so the decision can be revisited deliberately.
