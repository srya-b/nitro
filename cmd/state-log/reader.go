package main

import (
	"encoding/json"
	"fmt"
	"io/ioutil"
	_"math/big"
	"os"
	"strings"
	"strconv"
	"sort"

	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/log"
)

type Prepost int

const (
	PRE Prepost = iota
	POST
)

// LogFile represents a log file with its name and the first number for sorting.
type LogFile struct {
	FileName string
	Blockno  int
	Type     Prepost
	Count    int
}

func (l LogFile) String() string {
	return l.FileName
}

// ByNum implements the sort.Interface for sorting LogFile slices by the 'Num' field.
type ByBlock []LogFile
type ByTotalOrder []LogFile

func (a ByBlock) Len() int           { return len(a) }
func (a ByBlock) Swap(i, j int)      { a[i], a[j] = a[j], a[i] }
func (a ByBlock) Less(i, j int) bool { return a[i].Blockno < a[j].Blockno }

func (a ByTotalOrder) Len() int		 		{ return len(a) }
func (a ByTotalOrder) Swap(i, j int)		{ a[i], a[j] = a[j], a[i] }
func (a ByTotalOrder) Less(i, j int) bool {
	return a[i].Count < a[j].Count
}


//func (a ByTotalOrder) Less(i, j int) bool {
//	if a[i].Type == PRE && a[j].Type == PRE {
//		return a[i].Count < a[j].Count
//	} else if a[i].Type == PRE && a[j].Type == POST {
//		// if they have the same count then PRE is earlier than POST
//		if a[i].Count == a[j].Count {
//			return true
//		} else {
//			return a[i].Count < a[j].Count
//		}
//	} else if a[i].Type == POST && a[j].Type == PRE {
//		if a[i].Count == a[j].Count {
//			return false
//		} else {
//			return a[i].Count < a[j].Count
//		}
//	} else if a[i].Type == POST && a[j].Type == POST {
//		return a[i].Count < a[j].Count
//	} else {
//		panic(fmt.Sprintf("unknown type combo: %v, %v", a[i], a[j]))
//	}
//}

func getLogFilesSorted(dir string) [][]LogFile {
	var logFiles []LogFile
	files, err := os.ReadDir(dir)
	if err != nil {
		panic(fmt.Sprintf("Error reading dir %v", err))
	}

	for _, file := range files {
		if file.IsDir() {
			continue
		}

		filename := file.Name()
		// Check if the filename matches the format "string-number-number.json"
		if strings.HasSuffix(filename, ".json") {
			parts := strings.Split(strings.TrimSuffix(filename, ".json"), "-")
			if len(parts) == 3 {
				var preorpost Prepost
				if parts[0] == "predata" {
					preorpost = PRE
				} else if parts[0] == "postdata" {
					preorpost = POST
				} else {
					panic(fmt.Sprintf("file is neither predata or postdata : %v", parts[0]))
				}

				blockno, err := strconv.Atoi(parts[1])
				if err != nil {
					panic(fmt.Sprintf("Blockno couldn't be read as an int: %v", parts[1]))
				}
				iteration, err := strconv.Atoi(parts[2])
				if err != nil {
					panic(fmt.Sprintf("Iteration couldn't be read as an int: %v", parts[2]))
				}

				lf := LogFile{
					FileName: filename,
					Blockno: blockno,
					Type: preorpost,
					Count: iteration,
				}
				logFiles = append(logFiles, lf)
			}
		}
	}

	sort.Sort(ByBlock(logFiles))

	// group them by block number in a 2d array
	var groupedLogFiles [][]LogFile
	currBlockno := 0
		
	for _, lf := range logFiles {
		if lf.Blockno != currBlockno {
			groupedLogFiles = append(groupedLogFiles, []LogFile{})
			currBlockno = lf.Blockno
		}
		groupedLogFiles[len(groupedLogFiles)-1] = append(groupedLogFiles[len(groupedLogFiles)-1], lf)
	}

	// sanitycheck
	numsSeen := make(map[int]bool)
	for _, lfs := range groupedLogFiles {
		if len(lfs) > 0 {
			n := lfs[0].Blockno
			_, ok := numsSeen[n]
			if ok {
				panic(fmt.Sprintf("Seen this index already: %v", lfs))
			}
			numsSeen[n] = true
			for _, lf := range lfs {
				if lf.Blockno != n {
					panic(fmt.Sprintf("Not grouped correctly: %v", lfs))
				}		
			}
			sort.Sort(ByTotalOrder(lfs))
		}
	}

	log.Debug("Grouped log files", "sample", groupedLogFiles[0])
	return groupedLogFiles
}

func readPre(b int, v int) ([]byte, error) {
//func readPre(lf LogFile) ([]byte, error) {
	fn := fmt.Sprintf("%s/predata-%v-%d.json", logDir, b, v)
	log.Info("preLog", "file", fn)
	f, err := os.Open(fn)
	if err != nil {
		return nil, err
	}
	defer f.Close()

	content, err := ioutil.ReadFile(fn)
	if err != nil {
		return nil, err
	}
	return content, nil
}

func readPost(b  int, v int) ([]byte, error) {
//func readPost(lf LogFile) ([]byte, error) {
	fn := fmt.Sprintf("%s/postdata-%v-%d.json", logDir, b, v)
	//fn := lf.FileName
	log.Info("Getting Post", "fn", fn)
	f, err := os.Open(fn)
	if err != nil {
		return nil, err
	}
	defer f.Close()

	content, err := ioutil.ReadFile(fn)
	if err != nil {
		return nil, err
	}
	return content, nil
}

func preFromBytes(b []byte) *state.PreLog {
	var obj state.PreLog
	err := json.Unmarshal(b, &obj)
	if err != nil {
		panic(err)
	}
	return &obj
}

func postFromBytes(b []byte) *state.PostLog {
	var obj state.PostLog
	err := json.Unmarshal(b, &obj)
	if err != nil {
		panic(err)
	}
	return &obj
}

//func getPreObj(blockno *big.Int, version int) (*state.PreLog, bool) {
func getPreObj(blockno int, version int) (*state.PreLog, bool) {
	content, err := readPre(blockno, version)
	if err != nil {
		log.Error("No pre file", "e", err, "version", version)
		return nil, false
	}
	preObj := preFromBytes(content)
	// samplePreData(preObj)
	return preObj, true
}

func getPostObj(blockno int, version int) (*state.PostLog, bool) {
	content, err := readPost(blockno, version)
	if err != nil {
		log.Error("No post file", "err", err, "version", version)
		return nil, false
	}
	postObj := postFromBytes(content)
	// samplePostData(postObj)
	return postObj, true
}

func getPrePostObjs(blockno int, version int) (*state.PreLog, *state.PostLog, bool) {
	preObj, exists := getPreObj(blockno, version)
	if !exists {
		return nil, nil, false
	}

	postObj, exists := getPostObj(blockno, version)
	if !exists {
		log.Error("Prelog exists and postLog doesn't", "blockno", blockno, "version", version)
		panic("Missing postLog")
	}
	return preObj, postObj, true
}

