package main

import (
	"strings"
	"math/big"

	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/common"
)

type KeyPair struct {
	Address		common.Address	`json:"address"`
	Key			common.Hash		`json:"key"`
}

const (
	OPCODE		= "opcode"	
	BALANCE		= "balance"
	HOOK		= "hook"
	NONCE		= "nonce"
	ARB			= "arb"
	ARBTRANSFER = "arbtransfer"
	CODE		= "code"
)

type KeyAccess struct {
	Type		string		`json:"type"`
	Pair		KeyPair		`json:"pair"`
}

// TxTrace holds all state changes for a single transaction.
type TxTrace struct {
	BlockNumber *big.Int       		`json:"blockNumber"`
	TxIndex     	uint            `json:"txIndex"`
	TxHash			common.Hash	   `json:"txHash,omitempty"`
	WriteAccesses	[]KeyAccess		`json:"writes"`
	ReadAccesses	[]KeyAccess		`json:"reads"`
	CumulativeGas	uint64			`json:"cumulativeGas"`
	GasUsed			uint64			`json:"gasUsed"`
	GasUsedForL1	uint64			`json:"gasUsedForL1"`
	TxType			uint8			`json:"type"`
}

// BlockTrace is the final output file, containing all tx traces for a block.
type BlockTrace struct {
	BlockNumber *big.Int   `json:"blockNumber"`
	Traces      []*TxTrace  `json:"transactions"`
}

type AccessType uint8 // uint8 is enough for 7 flags (up to 8)

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

// accessTypeMap maps the string constants to their bit flag.
var accessTypeMap = map[string]AccessType{
	OPCODE:      AccessOpcode,
	BALANCE:     AccessBalance,
	HOOK:        AccessHook,
	NONCE:       AccessNonce,
	ARB:         AccessArb,
	ARBTRANSFER: AccessArbTransfer,
	CODE:        AccessCode,
}

func FilterAccesses(txTrace *TxTrace, filterFlags AccessType) ([]KeyAccess, []KeyAccess) {
	var filteredWrites []KeyAccess
	var filteredReads []KeyAccess

	// Return empty slices if the trace is nil
	if txTrace == nil {
		return filteredWrites, filteredReads
	}

	// Helper function to process a list of accesses
	// It appends matching items from 'source' to 'dest' and returns the new 'dest' slice.
	appendFiltered := func(dest []KeyAccess, source []KeyAccess) []KeyAccess {
		for _, access := range source {
			// 1. Look up the bit flag for the access's string Type
			if flag, ok := accessTypeMap[access.Type]; ok {
				
				// 2. Use a bitwise AND to check if the flag is set in the filter
				if (filterFlags & flag) != 0 {
					dest = append(dest, access)
				}
			}
		}
		return dest
	}

	// Process both writes and reads for this single transaction
	filteredWrites = appendFiltered(filteredWrites, txTrace.WriteAccesses)
	filteredReads = appendFiltered(filteredReads, txTrace.ReadAccesses)

	return filteredWrites, filteredReads
}

var stringToFlagMap = map[string]AccessType{
	"opcode":      AccessOpcode,
	"balance":     AccessBalance,
	"hook":        AccessHook,
	"nonce":       AccessNonce,
	"arb":         AccessArb,
	"arbtransfer": AccessArbTransfer,
	"code":        AccessCode,
	"all":         AccessAll, // Add an "all" shortcut
}

var orderedFlagNames = []string{
	"opcode",
	"balance",
	"hook",
	"nonce",
	"arb",
	"arbtransfer",
	"code",
}

func parseTypesFlag(typesStr string) AccessType {
	var filterFlags AccessType = 0 // Start with no flags set

	// Split the string by commas
	types := strings.Split(typesStr, ",")

	for _, t := range types {
		// Clean up whitespace and convert to lowercase
		t = strings.ToLower(strings.TrimSpace(t))
		
		if t == "" {
			continue
		}

		// Look up the string in our new map
		if flag, ok := stringToFlagMap[t]; ok {
			// This is the key: use bitwise OR to add the flag
			// to our filter.
			filterFlags |= flag
		} else {
			log.Warn("Warning: unknown access type '%s', skipping", t)
		}
	}
	
	// If the user passed "all", the 'filterFlags' will now contain the 'AccessAll' bits.
	// If the user passed "balance,nonce", it will contain 'AccessBalance | AccessNonce'.
	// If the string was empty, it will return 0 (no flags).
	return filterFlags
}

func FormatAccessFlags(filterFlags AccessType) string {
	// Handle special cases first
	if filterFlags == 0 {
		return "(None)" // Or return "" if you prefer
	}
	if filterFlags == AccessAll {
		return "all"
	}

	var parts []string

	// Iterate over our ordered list to ensure consistent output
	for _, name := range orderedFlagNames {
		// Look up the bit flag for this name
		flag, ok := stringToFlagMap[name]
		if !ok {
			continue // Should never happen if maps are in sync
		}

		// Check if this flag's bit is set in the input
		if (filterFlags & flag) != 0 {
			parts = append(parts, name)
		}
	}

	return strings.Join(parts, ",")
}
