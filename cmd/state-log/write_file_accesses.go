package main

import (
	"os"
	"fmt"
	"sort"
	"encoding/json"
	
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/state"
)

func setToSlice(set map[state.KeyKey]bool) []state.KeyKey {
	out := make([]state.KeyKey, 0, len(set))
	for k := range set {
		out = append(out, k)
	}
	return out
}

// The internal data structure is now:
// Block number (int) -> [][]KeyKey (list of alternating [Read, Write] slices across all transactions)
var blockAccessData = make(map[int][][]state.KeyKey) 

// ... (setToSlice function remains the same)

// StoreBlockAccesses processes the transaction access sets for a block,
// converts them to alternating Read and Write slices, and stores them internally.
//
// blockNumber: The block number.
// txAccesses: A list of access sets for transactions in the block.
//             [0] = Tx1 Read set, [1] = Tx1 Write set, [2] = Tx2 Read set, etc.
func StoreBlockAccesses(blockNumber int, txAccesses []map[state.KeyKey]bool) error {
    // Input validation: Check that the length of txAccesses is a multiple of 2.
    if len(txAccesses)%2 != 0 {
        return fmt.Errorf("input txAccesses for block %d must be a multiple of 2, but got %d", blockNumber, len(txAccesses))
    }

	// blockData will be a flat slice containing [Tx1_R, Tx1_W, Tx2_R, Tx2_W, ...]
	blockData := make([][]state.KeyKey, len(txAccesses))

	for i := 0; i < len(txAccesses); i += 2 {
		readSet := txAccesses[i]
		writeSet := txAccesses[i+1]

        // 1. Convert Read Set to Slice
		readSlice := setToSlice(readSet)
		
        // 2. Convert Write Set to Slice
		writeSlice := setToSlice(writeSet)

        // 3. Store the two slices sequentially in the main blockData slice.
        // This preserves the alternating pattern: R, W, R, W, ...
		blockData[i] = readSlice
		blockData[i+1] = writeSlice
	}

	blockAccessData[blockNumber] = blockData
    return nil // Success
}

// KeyKeyJSON is the concrete type used for JSON serialization.
type KeyKeyJSON struct {
	Addr common.Address
	Key  common.Hash
}

// BlockAccessJSON is the structure that will be serialized to the file.
// Accesses is the two-dimensional slice: []AccessList []KeyKeyJSON
type BlockAccessJSON struct {
	BlockNumber int
	Accesses    [][]KeyKeyJSON // Correct for the [][]KeyKey internal structure
}

// The entire file content will be a slice of these structs.
type FileData []BlockAccessJSON

// WriteBlockAccesses serializes all stored block data to the specified file.
// It converts the internal [][]KeyKey to [][]KeyKeyJSON for serialization.
func WriteBlockAccesses(filePath string) error {
	var fileData FileData

	// Sort block numbers for consistent file output
	var blockNumbers []int
	for blockNum := range blockAccessData {
		blockNumbers = append(blockNumbers, blockNum)
	}
	sort.Ints(blockNumbers)

	// Convert internal KeyKey data (interface) to JSON-serializable KeyKeyJSON data (concrete)
	for _, blockNum := range blockNumbers {
		blockData := blockAccessData[blockNum]
		jsonAccesses := make([][]KeyKeyJSON, len(blockData))
		
		for i, accessList := range blockData {
			accessListJSON := make([]KeyKeyJSON, len(accessList))
			for j, key := range accessList {
				accessListJSON[j] = KeyKeyJSON{
					Addr: key.Addr(),
					Key:  key.Key(),
				}
			}
			jsonAccesses[i] = accessListJSON
		}

		fileData = append(fileData, BlockAccessJSON{
			BlockNumber: blockNum,
			Accesses:    jsonAccesses,
		})
	}

	// Marshal the entire data structure
	data, err := json.MarshalIndent(fileData, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal block access data: %w", err)
	}

	// Write to file
	if err := os.WriteFile(filePath, data, 0644); err != nil {
		return fmt.Errorf("failed to write block access data to file: %w", err)
	}

	return nil
}

// ReadBlockAccesses reads the block access data from the specified file,
// returns the data and the lowest block number, or an error.
func ReadBlockAccesses(filePath string) (map[int][][]state.KeyKey, int, error) {
	data, err := os.ReadFile(filePath)
	if err != nil {
		return nil, 0, fmt.Errorf("failed to read file: %w", err)
	}

	var fileData FileData
	if err := json.Unmarshal(data, &fileData); err != nil {
		return nil, 0, fmt.Errorf("failed to unmarshal block access data: %w", err)
	}

	resultData := make(map[int][][]state.KeyKey)
	lowestBlockNum := -1 // Initialize with a value that indicates 'not set'

	for _, block := range fileData {
		// Convert KeyKeyJSON (concrete) back to KeyKey interface implementations
		blockAccesses := make([][]state.KeyKey, len(block.Accesses))
		for i, accessListJSON := range block.Accesses {
			accessList := make([]state.KeyKey, len(accessListJSON))
			for j, k := range accessListJSON {
				// Store as a concrete type that implements the KeyKey interface
				accessList[j] = state.NewKeyKey(k.Addr, k.Key)
			}
			blockAccesses[i] = accessList
		}
		
		resultData[block.BlockNumber] = blockAccesses

		// Track the lowest block number
		if lowestBlockNum == -1 || block.BlockNumber < lowestBlockNum {
			lowestBlockNum = block.BlockNumber
		}
	}

	return resultData, lowestBlockNum, nil
}
