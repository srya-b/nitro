package main

import (
	"fmt"
	"sort"
)

func numTxs(datadir string) int {
	sortedFiles, err := getSortedTraceFiles(datadir)
	if err != nil {
		fmt.Printf("Failed with error: %v\n", err)
		return 1
	}

	fmt.Printf("Num blocks: %d\n", len(sortedFiles))

	txCounts := make([]int, 0, len(sortedFiles))
	for _, file := range sortedFiles {
		trace, err := BlockTraceFromFile(file)
		if err != nil {
			fmt.Println(err)
			return 1
		}
		txCounts = append(txCounts, len(trace.Traces))
	}

	histogram := createHistogram(txCounts, 1)
	var keys []int
	for key := range histogram {
		keys = append(keys, key)
	} 

	sort.Ints(keys)
	fmt.Printf("Block length histogram\n")
	for _, key := range keys {
		fmt.Printf("[%d]:%d\n", key, histogram[key])
	}
	return 0
}
