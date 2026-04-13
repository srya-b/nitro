package main

import (
	"os"
	"fmt"
	"sort"
	"regexp"
	"strconv"
	"path/filepath"
	"encoding/json"

	"github.com/ethereum/go-ethereum/log"
)

type fileWithNum struct {
	path string // The full path to the file
	num  int    // The extracted integer
}

func getUnsortedTraceFiles(datadir string) ([]fileWithNum, error) {
	pattern := `^state_trace_block_(\d+)\.json$`
	re, err := regexp.Compile(pattern)
	if err != nil {
		return nil, fmt.Errorf("failed to compile regex: %w", err)
	}

	entries, err := os.ReadDir(datadir)
	if err != nil {
		return nil, fmt.Errorf("failed to read directory '%s': %w", datadir, err)
	}

	var matchedFiles []fileWithNum

	// 3. Iterate over files, filter by regex, and parse
	for _, entry := range entries {
		// Skip subdirectories
		if entry.IsDir() {
			continue
		}

		filename := entry.Name()
		
		// re.FindStringSubmatch returns a slice of strings.
		// matches[0] is the full matched string (e.g., "state_trace_block_123.json")
		// matches[1] is the first capture group (e.g., "123")
		matches := re.FindStringSubmatch(filename)

		if len(matches) == 2 {
			// We found a match. Parse the number (matches[1]).
			numStr := matches[1]
			num, err := strconv.Atoi(numStr)
			if err != nil {
				// This could happen if the number is too large or malformed,
				// but our regex (\d+) prevents malformed.
				log.Warn("Wathing: Skipping file, could not parse number", "filename", filename, "numStr", numStr, "err", err)
				continue
			}

			// Store the full path and the parsed number
			fullPath := filepath.Join(datadir, filename)
			matchedFiles = append(matchedFiles, fileWithNum{path: fullPath, num: num})
		}
	}

	return matchedFiles, nil
}

func getSortedTraceFiles(datadir string) ([]fileWithNum, error) {
	// 1. trying to math the files that are /datadir/state_trace_block_%d.json
	pattern := `^state_trace_block_(\d+)\.json$`
	re, err := regexp.Compile(pattern)
	if err != nil {
		return nil, fmt.Errorf("failed to compile regex: %w", err)
	}

	// 2. all files from the directory
	entries, err := os.ReadDir(datadir)
	if err != nil {
		return nil, fmt.Errorf("failed to read directory '%s': %w", datadir, err)
	}

	var matchedFiles []fileWithNum

	// 3. Iterate over files, filter by regex, and parse
	for _, entry := range entries {
		// Skip subdirectories
		if entry.IsDir() {
			continue
		}

		filename := entry.Name()
		
		// re.FindStringSubmatch returns a slice of strings.
		// matches[0] is the full matched string (e.g., "state_trace_block_123.json")
		// matches[1] is the first capture group (e.g., "123")
		matches := re.FindStringSubmatch(filename)

		if len(matches) == 2 {
			// We found a match. Parse the number (matches[1]).
			numStr := matches[1]
			num, err := strconv.Atoi(numStr)
			if err != nil {
				// This could happen if the number is too large or malformed,
				// but our regex (\d+) prevents malformed.
				log.Warn("Wathing: Skipping file, could not parse number", "filename", filename, "numStr", numStr, "err", err)
				continue
			}

			// Store the full path and the parsed number
			fullPath := filepath.Join(datadir, filename)
			matchedFiles = append(matchedFiles, fileWithNum{path: fullPath, num: num})
		}
	}

	// 4. sort files based on block number
	sort.Slice(matchedFiles, func(i, j int) bool {
		return matchedFiles[i].num < matchedFiles[j].num
	})

	return matchedFiles, nil
}

func BlockTraceFromFile(fn fileWithNum) (*BlockTrace, error) {
	jsonFile, err := os.Open(fn.path)
	if err != nil {
		return nil, err
	}
	
	defer jsonFile.Close()

	decoder := json.NewDecoder(jsonFile)
	
	var trace BlockTrace
	
	err = decoder.Decode(&trace)
	if err != nil {
		return nil, err 
	}

	return &trace, nil
}

func BlockTraceMetaDataFromFile(fn fileWithNum) (*BlockTraceMetaData, error) {
	jsonFile, err := os.Open(fn.path)
	if err != nil {
		return nil, err
	}
	
	defer jsonFile.Close()

	decoder := json.NewDecoder(jsonFile)
	
	var trace BlockTraceMetaData
	
	err = decoder.Decode(&trace)
	if err != nil {
		return nil, err 
	}

	return &trace, nil
}
