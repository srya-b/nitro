package main

import (
    "reflect"

	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/core/state"
)

func WriteBlockAccessesToFile(dir string, limit int, outfn string) {
    logFiles := getLogFilesSorted(dir)
    prevBlock := 0
    for i, blockLogs := range logFiles {
        if i >= limit {
            break
        }
        txAccesses := BlockReadWriteAccesses(blockLogs)
        if len(txAccesses) > 0 {
            blockno := blockLogs[0].Blockno
            prevBlock = blockno
            StoreBlockAccesses(blockno, txAccesses)
        } else {
            if len(blockLogs) > 0 {
                blockno := blockLogs[0].Blockno
                prevBlock = blockno
                log.Debug("Block has no usable data", "block", blockno)
                if len(blockLogs) > 1 {
                    panic("")
                }
             } else {
                log.Error("Empty Block", "prevblock", prevBlock)
             }
        }
    }
    WriteBlockAccesses(outfn)
}

// Check that the function code for writing block accesses to file writes the same
// blocks to file as the code that computes conflicts live.
func CheckSameBlocksWritten(dir string, limit int) {
    logFiles := getLogFilesSorted(dir)
    blocksIncludedByFileAccesses := make(map[int]bool)
    blocksIncludedByChecker := make(map[int]bool)
    prevBlock := 0

    for i, blockLogs := range logFiles {
        if i >= limit {
            break
        }
        txAccesses := BlockReadWriteAccesses(blockLogs)
        if len(txAccesses) > 0 {
            blockno := blockLogs[0].Blockno
            prevBlock = blockno
            blocksIncludedByFileAccesses[blockno] = true
        } else {
            if len(blockLogs) > 0 {
                blockno := blockLogs[0].Blockno
                prevBlock = blockno
                log.Debug("Block has no usable data", "block", blockno)
                if len(blockLogs) > 1 {
                    panic("")
                }
             } else {
                log.Error("Empty Block", "prevblock", prevBlock)
             }
        }
        graph, b := BlockGraph(blockLogs) 
        if graph != nil {
            blocksIncludedByChecker[b] = true
        }
    }

    if !reflect.DeepEqual(blocksIncludedByFileAccesses, blocksIncludedByChecker) {
        log.Error("They aren't the same", "file", len(blocksIncludedByFileAccesses), "checker", len(blocksIncludedByChecker), "diff", mapDiff(blocksIncludedByFileAccesses, blocksIncludedByChecker))
        panic("")
    }
}

// check that the file contains the same data
func ValidateBlockAccessesFile(dir string, limit int, infn string) {
    logFiles := getLogFilesSorted(dir)
    accessLists, _, err := ReadBlockAccesses(infn)
    if err != nil {
        log.Error("Couldn't read accesses from file", "file", infn)
        panic(err)
    }
    
    for i, blockLogs := range logFiles {
        if i >= limit {
            break
        }

        if len(blockLogs) > 1 {
            blockno := blockLogs[0].Blockno
            fileAccesses, exists := accessLists[blockno]
            if exists {
                if !EqualBlockAccesses(blockLogs, fileAccesses) {
                    log.Error("Unequal accesses")
                    panic("")
                }
            } else {
                log.Error("blocklogs exists but not in file", "block", blockno)
            }
        }   
    }
    
}

func BlockReadWriteAccesses(blockLogs []LogFile) []map[state.KeyKey]bool {
    txAccesses := []map[state.KeyKey]bool{}
	for i := 0; i < len(blockLogs) - 1; i += 2 {
        pre := blockLogs[i]
        post := blockLogs[i+1]
        if pre.Type == PRE && post.Type == POST {
			// we only care about pre because those are what's needed for execution
			preObj, _ := getPreObj(pre.Blockno, pre.Count)
			if ignoreJournal(preObj.Journals) {
				continue
			}
			if ok := CheckRoot(preObj); !ok {
				continue
			}

			// each journal in preObj.Journals is taken to be a single message/tx
			ejournals := state.JournalsToExported(preObj.Journals)
			for _, journal := range ejournals {
                txReads := make(map[state.KeyKey]bool)
                txWrites := make(map[state.KeyKey]bool)
				// log the things
				reads := GetReadButNotWrite(journal)
				for kk := range reads {
                    txReads[kk] = true
				}
                txAccesses = append(txAccesses, txReads)
				// log the things it writes
				written := GetWrittenKeys(journal)
				for kk := range written {
                    txWrites[kk] = true
				}
                txAccesses = append(txAccesses, txWrites)
            }
        }
    }
    return txAccesses
}

func EqualBlockAccesses(blockLogs []LogFile, accesses [][]state.KeyKey) bool {
    txid := 0
    for i := 0; i < len(blockLogs) - 1; i += 2 {
        pre := blockLogs[i]
        post := blockLogs[i]
        if pre.Type == PRE && post.Type == POST {
			// we only care about pre because those are what's needed for execution
			preObj, _ := getPreObj(pre.Blockno, pre.Count)
			if ignoreJournal(preObj.Journals) {
				continue
			}
			if ok := CheckRoot(preObj); !ok {
				continue
			}
			// each journal in preObj.Journals is taken to be a single message/tx
			ejournals := state.JournalsToExported(preObj.Journals)
			for _, journal := range ejournals {
                txReads := make(map[state.KeyKey]bool)
                txWrites := make(map[state.KeyKey]bool)
                fileReads := listToSet(accesses[txid])
                fileWrites := listToSet(accesses[txid+1])
                reads := GetReadButNotWrite(journal)
				for kk := range reads {
                    txReads[kk] = true
				}
				// log the things it writes
				written := GetWrittenKeys(journal)
				for kk := range written {
                    txWrites[kk] = true
				}
                readsEqual := reflect.DeepEqual(fileReads, txReads)
                writesEqual := reflect.DeepEqual(fileWrites, txWrites)
                if !readsEqual {
                    log.Error("Reads aren't equal")
                }
                if !writesEqual {
                    log.Error("Writes aren't equal")
                }
                if !readsEqual || !writesEqual {
                    return false
                }
                txid += 2
            }
        }
    }
    return true
}
