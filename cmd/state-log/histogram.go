package main

import (
	"os"
	"fmt"
	"sort"
	"bufio"
)

// createHistogram takes an input slice of integers and a bin width,
// and returns a map representing a histogram. The keys of the map
// are the starting values of each bin, and the values are the counts
// of elements falling into that bin.
func createHistogram(data []int, binWidth int) map[int]int {
	// Initialize an empty map to store the histogram bins.
	// The key is the bin's starting value, and the value is the count.
	histogram := make(map[int]int)

	// Iterate over each element in the input slice.
	for _, value := range data {
		// Calculate the start of the bin for the current value.
		// Integer division is used to find which bin the value belongs to.
		// For example, if binWidth is 10000:
		// - A value of 5000 will result in binStart = (5000 / 10000) * 10000 = 0.
		// - A value of 15000 will result in binStart = (15000 / 10000) * 10000 = 10000.
		binStart := (value / binWidth) * binWidth

		// Increment the count for the corresponding bin.
		// If the bin doesn't exist yet, it will be automatically created with a value of 0 before incrementing.
		histogram[binStart]++
	}

	return histogram
}

// writeHistogramToFile writes the histogram data to a specified file path in a simple CSV format.
func writeHistogramToFile(histogram map[int]int, filePath string, binWidth int) error {
	file, err := os.Create(filePath)
	if err != nil {
		return fmt.Errorf("failed to create file: %w", err)
	}
	defer file.Close()

	writer := bufio.NewWriter(file)
	// Write header for the CSV file.
	_, err = writer.WriteString("BinStart,Count\n")
	if err != nil {
		return fmt.Errorf("failed to write header: %w", err)
	}

	// Get a sorted list of keys to write the data in order.
	var keys []int
	for key := range histogram {
		keys = append(keys, key)
	}
	sort.Ints(keys)

	for _, key := range keys {
		// Write each bin's data to a new line.
		line := fmt.Sprintf("%d,%d\n", key, histogram[key])
		_, err := writer.WriteString(line)
		if err != nil {
			return fmt.Errorf("failed to write line: %w", err)
		}
	}

	return writer.Flush()
}

func HistogramWriteFile(data []int, binWidth int, filePath string) {
	// Sample input data.
	//data := []int{
	//	1234, 5678, 11000, 19500, 23000, 28000, 31000, 45000, 50000, 50001,
	//	50005, 59999, 60000, 65000, 72000, 80000, 85000, 99999, 100000,
	//}
	//filePath := "block-histogram.csv"

	// Create the histogram.
	histogram := createHistogram(data, binWidth)

	// Write the histogram to the CSV file.
	err := writeHistogramToFile(histogram, filePath, binWidth)
	if err != nil {
		fmt.Printf("Error writing histogram to file: %s\n", err)
	} else {
		fmt.Printf("Successfully wrote histogram data to %s\n", filePath)
	}

	// Get a sorted list of keys to print the histogram in order.
	var keys []int
	for key := range histogram {
		keys = append(keys, key)
	}
	sort.Ints(keys)

	// Print the histogram.
	fmt.Printf("Histogram with a bin width of %d:\n", binWidth)
	for _, key := range keys {
		// A histogram visually represents data distribution, with bin width as the x-axis unit.
		fmt.Printf("[%d - %d]: %d elements\n", key, key+binWidth-1, histogram[key])
	}
}
