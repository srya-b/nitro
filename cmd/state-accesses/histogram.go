package main

import (
	"os"
	"fmt"
	"sort"
	"math"
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

func writeSpeedupsToFile(blockSpeedups []*BlockSpeedup, filePath string) error {
	file, err := os.Create(filePath)
	if err != nil {
		return fmt.Errorf("failed to create file: %w", err)
	}
	defer file.Close()

	writer := bufio.NewWriter(file)
	// Write header for the CSV file.
	_, err = writer.WriteString("BlockNumber,Cores,Sequential,Concurrent\n")	
	if err != nil {
		return fmt.Errorf("failed to write header: %w", err)
	}

	for _, bs := range blockSpeedups {
		for k, concurrent := range bs.Equivalent {
			line := fmt.Sprintf("%d,%d,%d,%d\n", bs.BlockNumber, k, bs.Sequential, concurrent)
			_, err := writer.WriteString(line)
			if err != nil {
				return fmt.Errorf("failed to write line: %w", err)
			}
		}
	}
	return writer.Flush()
}

func appendSpeedupsToFile(blockSpeedups []*BlockSpeedup, filePath string) {
    f, err := os.OpenFile(filePath, os.O_APPEND|os.O_WRONLY, 0644)
    if err != nil { return }
    defer f.Close()
    
    writer := bufio.NewWriter(f)
    for _, bs := range blockSpeedups {
        for k, concurrent := range bs.Equivalent {
            line := fmt.Sprintf("%d,%d,%d,%d\n", bs.BlockNumber, k, bs.Sequential, concurrent)
            writer.WriteString(line)
        }
    }
    writer.Flush()
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

// createFloatHistogram takes an input slice of float64 and a bin width (float64),
// and returns a map representing a histogram.
func createFloatHistogram(data []float64, binWidth float64) map[float64]int {
	histogram := make(map[float64]int)

	for _, value := range data {
		// Calculate the bin index: value / binWidth
		// Use math.Floor to ensure the bin start is consistently calculated.
		binStart := math.Floor(value/binWidth) * binWidth
		//fmt.Printf("[%d] stats. value: %v, binWidth %v, binStart %v\n", i, value, binWidth, binStart)
		histogram[binStart]++
	}
	return histogram
}

// writeFloatHistogramToFile writes the float64 histogram data to a specified file path in a simple CSV format.
func writeFloatHistogramToFile(histogram map[float64]int, filePath string, binWidth float64) error {
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

	// Get a sorted list of float64 keys to write the data in order.
	var keys []float64
	for key := range histogram {
		keys = append(keys, key)
	}
	sort.Float64s(keys) // Use sort.Float64s for sorting float keys

	for _, key := range keys {
		// Use %g for a clean, general float representation in the output file.
		line := fmt.Sprintf("%g,%d\n", key, histogram[key])
		_, err := writer.WriteString(line)
		if err != nil {
			return fmt.Errorf("failed to write line: %w", err)
		}
	}

	return writer.Flush()
}


func FloatHistogramWriteFile(floatData []float64, floatBinWidth float64, floatFilePath string) {
	//// Create the histogram.
	//histogram := createHistogram(data, binWidth)

	//// Write the histogram to the CSV file.
	//err := writeHistogramToFile(histogram, filePath, binWidth)
	//if err != nil {
	//	fmt.Printf("Error writing histogram to file: %s\n", err)
	//} else {
	//	fmt.Printf("Successfully wrote histogram data to %s\n", filePath)
	//}

	//// Get a sorted list of keys to print the histogram in order.
	//var keys []int
	//for key := range histogram {
	//	keys = append(keys, key)
	//}
	//sort.Ints(keys)

	//// Print the histogram.
	//fmt.Printf("Histogram with a bin width of %d:\n", binWidth)
	//for _, key := range keys {
	//	// A histogram visually represents data distribution, with bin width as the x-axis unit.
	//	fmt.Printf("[%d - %d]: %d elements\n", key, key+binWidth-1, histogram[key])
	//}

	//floatData := []float64{
	//	0.12, 0.25, 1.05, 1.15, 1.99, 2.00, 2.01, 3.45, 3.50, 4.01,
	//	4.10, 4.25, 4.99, 5.00, 5.001, 5.9, 6.7, 7.8, 8.99, 9.99, 10.0, 10.00001,
	//}
	//floatBinWidth := 1.0
	//floatFilePath := "float_histogram.csv"

	// Create and write the float histogram.
	floatHistogram := createFloatHistogram(floatData, floatBinWidth)
	err := writeFloatHistogramToFile(floatHistogram, floatFilePath, floatBinWidth)
	if err != nil {
		fmt.Printf("Error writing float histogram to file: %s\n", err)
	} else {
		fmt.Printf("Successfully wrote float histogram data to %s\n", floatFilePath)
	}

	// Print the float histogram.
	fmt.Printf("\n--- Float64 Histogram (Bin Width: %g) ---\n", floatBinWidth)
	var floatKeys []float64
	for key := range floatHistogram {
		floatKeys = append(floatKeys, key)
	}
	sort.Float64s(floatKeys)
	for _, key := range floatKeys {
		// Use %g for clean float representation
		fmt.Printf("[%g - %g]: %d elements\n", key, key+floatBinWidth, floatHistogram[key])
	}
}

// mergeHistograms takes a master histogram and a chunk histogram,
// and adds the counts from the chunk into the master.
// The master histogram is modified in place.
func mergeHistograms(master map[int]int, chunk map[int]int) {
	for binStart, count := range chunk {
		// If the binStart key doesn't exist in master,
		// Go's default is 0, so (0 + count) works perfectly.
		master[binStart] += count
	}
}

// mergeFloatHistograms takes a master float64 histogram and a chunk histogram,
// and adds the counts from the chunk into the master.
// The master histogram is modified in place.
func mergeFloatHistograms(master map[float64]int, chunk map[float64]int) {
	for binStart, count := range chunk {
		master[binStart] += count
	}
}
