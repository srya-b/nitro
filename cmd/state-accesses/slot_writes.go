package main

import (
	"os"
	"io"
	"fmt"
	"sort"
	"math"
	"bufio"
	"slices"
	"strconv"
	"math/big"
	"encoding/csv"
	"github.com/ethereum/go-ethereum/common"
)

type HistogramLine struct {
	Address common.Address
	Key		common.Hash
	Count   int
}

func SumCountColumn(filename string) (int, int, error) {
	// 1. Open the file
	file, err := os.Open(filename)
	if err != nil {
		return 0, 0, fmt.Errorf("could not open file: %w", err)
	}
	defer file.Close()

	// 2. Create a CSV reader
	reader := csv.NewReader(file)

	// 3. Read and skip the header row
	// We assume the first row contains labels like "Count"
	_, err = reader.Read()
	if err != nil {
		return 0, 0, fmt.Errorf("error reading header: %w", err)
	}

	totalSum := 0
	numLines := 0

	// 4. Iterate through the records
	for {
		record, err := reader.Read()
		if err == io.EOF {
			break // End of file reached
		}
		if err != nil {
			return 0, 0, fmt.Errorf("error reading csv record: %w", err)
		}

		// Safety check: ensure the row has at least 2 columns
		if len(record) < 2 {
			continue // specific logic for malformed rows can be added here
		}

		// 5. Parse the second column (index 1)
		// record[1] corresponds to the 2nd column
		countVal, err := strconv.Atoi(record[1])
		if err != nil {
			return 0, 0, fmt.Errorf("error converting value '%s' to int: %w", record[1], err)
		}

		numLines++
		// 6. Accumulate the sum
		totalSum += countVal
	}

	return totalSum, numLines, nil
}	

func slotWriteStats(histogram string) int {
	totalSum, numSlots, err := SumCountColumn(histogram)
	if err != nil {
		fmt.Println(err)
		return 1
	}
	fmt.Printf("Total writes: %d\n", totalSum)
	fmt.Printf("Total slots written: %d\n", numSlots)
	return 0
}

func slotGrowth(datadir string) int {
	files, err := getSortedTraceFiles(datadir)
	if err != nil {
		fmt.Printf("failed with error: %w\n", err)
		return 1
	}

	fmt.Printf("Num blocks: %d\n", len(files))

	block_step := 346300
	slots := make(map[KeyPair]bool)
	blocksProcessed := 0
	keysSeen := len(slots)
	incremental_gains := []int{}

	for _, file := range files {
		trace, err := BlockTraceFromFile(file)
		if err != nil {
			fmt.Println(err)
			return 1
		}
		
		if blocksProcessed == block_step {
			// difference between now and the last value in incremental
			diff := len(slots) - keysSeen	
			fmt.Printf("%d new keys\n", diff)
			incremental_gains = append(incremental_gains, diff)
			keysSeen = len(slots)
			blocksProcessed = 0
		}
		
		for _, txtrace := range trace.Traces {
			for _, write := range txtrace.WriteAccesses {
				if write.Type == OPCODE {
					if write.Pair.Key.Cmp(common.Hash{}) != 0 {
						// this isn't an address access
						slots[write.Pair] = true
					}
				}
			}
		}
		blocksProcessed++
	}

	fmt.Println(incremental_gains)
	return 0
	
}

func slotWrites(datadir string) int {
	files, err := getSortedTraceFiles(datadir)
	if err != nil {
		fmt.Printf("Failed with error: %w\n", err)
		return 1
	}

	fmt.Printf("Num blocks: %d\n", len(files))


	start := big.NewInt(0)
	end := big.NewInt(math.MaxInt64)


	// Aug 7
	//start := big.NewInt(365731022)
	//end := big.NewInt(366077342)

	// Aug 8
	//start := big.NewInt(366077343)
	//end := big.NewInt(366423713)

	// Aug 9
	//start := big.NewInt(366423714)
	//end := big.NewInt(366769920)

	// Aug 10
	//start := big.NewInt(366769921)
	//end := big.NewInt(367116112)

	slotWrites := make(map[KeyPair]int)
	for _, file := range files {
		trace, err := BlockTraceFromFile(file)
		if err != nil {
			fmt.Println(err)
			return 1
		}

		if trace.BlockNumber.Cmp(end) == 1 {
			break
		}

		if trace.BlockNumber.Cmp(start) == 0 || trace.BlockNumber.Cmp(start) == 1 {
			for _, txtrace := range trace.Traces {
				for _, write := range txtrace.WriteAccesses {
					if write.Type == OPCODE {
						if write.Pair.Key.Cmp(common.Hash{}) != 0 {
							// this isn't an address access
							slotWrites[write.Pair]++
						}
					}
				}
			}
		}


	}

	writeCounts := make([]HistogramLine, len(slotWrites))
	for pair, count := range slotWrites {
		writeCounts = append(writeCounts, HistogramLine{pair.Address, pair.Key, count})
	}

	slices.SortFunc(writeCounts, func(a, b HistogramLine) int {
		return b.Count - a.Count
	})

	histogram := make(map[int]HistogramLine)
	fmt.Printf("Slot writes histogram\n")
	for i, line := range writeCounts {
		if i < 50 {
			fmt.Printf("%d\n", line.Count)
		}
		histogram[i] = line
	}

	writeKeysToFile(histogram, "/home/admin/surya/slot-writes-Aug10.csv", 1)

	return 0
}

func writeKeysToFile(histogram map[int]HistogramLine, filePath string, binWidth int) error {
	file, err := os.Create(filePath)
	if err != nil {
		return fmt.Errorf("failed to create file: %w", err)
	}
	defer file.Close()

	writer := bufio.NewWriter(file)
	_, err = writer.WriteString("BinStart,Count,Address,Key\n")
	if err != nil {
		return fmt.Errorf("failed to write header: %w", err)
	}

	var keys []int
	for key := range histogram {
		keys = append(keys, key)
	}
	sort.Ints(keys)

	for _, key := range keys {
		entry, _ := histogram[key]
		line := fmt.Sprintf("%d,%d,%x,%x\n", key, entry.Count, entry.Address, entry.Key)
		_, err := writer.WriteString(line)
		if err != nil {
			return fmt.Errorf("failed to write line: %w\n", err)
		}
	}

	return writer.Flush()
}

// we care about percent reads/writes
// percent insert/delete
func activityStats(datadir string) int {
	// get all block traces

	// track the number of reads and writes
	// the number of inserts/deletes
