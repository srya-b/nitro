This program takes data captured via the `go-ethereum/eth/tracers/live/storagetracer.go` live tracer.

Build the executable with `make target/bin/state-accesses` (the target is already a part of the nitro Makefile.

## Usage
The processor is called via

`./target/bin/state-accesses [--batches b] [--limit l] [--debug] <data directory> <output directory?`

The executable reads data files (one per block) from `<data directory>` whose names matche the regex `^state_trace_block(\d+)\.json$` (files like `state_trace_block_123456.json`), and processes them from lowest to highest block number. 
The program writes the output data to `<output directory>` in the form of a directory that specifies what parameters the data was processed with.

`--limit l`: limits the data processing to the first `l` blocks only (default: all files)

`--batches b`: breaks the data into `b` batches and processes them as such. The resulting histogram from each batch is saved, and they are all merged. This is useful if the data is so large it fills your memory and the os kills the process.

`--debug`: don't write anything to file

## Non-command line parameters
These are parameters that must be set in the code. I haven't added them as command-line parameters because it would be annoying to do or make the command-line call very verbose.

### Filtering data by access type
The data is all tagged by what kind of storage access it is:
```
const (
	OPCODE      = "opcode"
	BALANCE     = "balance"
	HOOK        = "hook"
	NONCE       = "nonce"
	ARB         = "arb"
	ARBTRANSFER = "arbtransfer"
	CODE        = "code"
)
```
`OPCODE` corresponds to straoge reads/writes from `SLOAD` and `SSTORE`.

`BALANCE` corresponds to reads via the `BALANCE` opcode and writes via account balance updates.

`HOOK` corresponds to only storage writes that change the value in the slot. Naturally, this is a subset of the `OPCODE` accesses.

`NONCE` corresponds to changes to the nonce of an account, and these accesses are only writes (no reads).

`ARB` corresponds to reads/writes to arbitrum storage (outside of the EVM). This is arbitrum specific data like the storage of the special address `0xA4b05FffffFffFFFFfFFfffFfffFFfffFfFfFFFf`.

`ARBTRANSFER` is arbitrum transfers (so it's only writes) initiated outside of EVM execution. These appear to correspond to transfers initiated by special arbitrum addresses oustide of EVM execution.

`CODE` changes are writes that change the codehash in an account in the state trie.

The accesses you want to include from the data can be specified through a series of flags.
```
const (
	// Use iota to assign powers of 2 automatically (1, 2, 4, 8, ...)
	AccessOpcode AccessType = 1 << iota // 1
	AccessBalance                       // 2
	AccessHook                          // 4
	AccessNonce                         // 8
	AccessArb                           // 16
	AccessArbTransfer                   // 32
	AccessCode                          // 64

	// A helper to select all types
	AccessAll = AccessOpcode | AccessBalance | AccessHook | AccessNonce |
				AccessArb | AccessArbTransfer | AccessCode
)
```

You can OR together any of the acess types you want inside the function `mainImpl()`. 
Currently, the default data set is `accessFlags := AccessOpcode | AccessCode`.

### Filtering data by address.
You can also filter the data used by adding an address to the map `FilterAddrs` in `state-accesses.go`.
This may be very important if you want to process many of the access types above, but filter out writes to the specific addresses.

Currently the filter only includes the arbos address `0xA4b05FffffFffFFFFfFFfffFfffFFfffFfFfFFFf`. 
If we want to include `BALANCE` data, then this filter is important otherwise you get NO speedup from parallel execution. 

**It remains to be determined whether this hinderance to parallel execution has an easy fix in the nitro code.**
