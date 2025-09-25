package main

import (
	"sort"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/core/state"
)


func ConcurrentRun(dir string) {
	logFiles := getLogFilesSorted(dir)

	for i, blockLogs := range logFiles {
		if i > 10 {
			break
		}
		BlockConflicts(blockLogs)
	}
}

var ConcurrentExcludeAddrs = map[common.Address]bool{
	common.HexToAddress("0xA4b05FffffFffFFFFfFFfffFfffFFfffFfFfFFFf"): true,
}

// Given a the log files for a block, what transactions conflict with each other,
// and what are the most common conflicting storage slots
// returns list of transactions have no conflicts
// returns the pairs of tranactions that conflict
// returns a map of storage slots -> number of transactions they are used by
func BlockConflicts(blockLogs []LogFile) ([]int, [][]int, map[state.KeyKey]int) {
	txWrites := make(map[state.KeyKey][]int)
	txReads := make(map[state.KeyKey][]int)

	txidx := 0
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
				// log the things it writes
				written := GetWrittenKeys(journal)
				for kk := range written {
					if _, ok := ConcurrentExcludeAddrs[kk.Addr()]; ok {
						// skip this addr and see what happens
						continue
					}
					_, ok := txWrites[kk]
					if !ok {
						txWrites[kk] = []int{}
					}
					txWrites[kk] = append(txWrites[kk], txidx)
				}
				// log the things
				reads := GetReadButNotWrite(journal)
				for kk := range reads {
					if _, ok := ConcurrentExcludeAddrs[kk.Addr()]; ok {
						// skip this addr and see what happens
						continue
					}
					_, ok := txReads[kk]
					if !ok {
						txReads[kk] = []int{}
					}
					txReads[kk] = append(txReads[kk], txidx)
				}
				txidx++
			}
		}
	}

	txConflicts := make(map[int]map[int]bool)
	
	// for each k in written: all txs in those conflict with each other and with all the ones that read it
	for _, txs := range txWrites {
		// all those transactions conflict with each other
		for _, tx := range txs {
			if _, ok := txConflicts[tx]; !ok {
				txConflicts[tx] = make(map[int]bool)
			}
			for _, othertx := range txs {
				if othertx != tx {
					txConflicts[tx][othertx] = true
				}
			}
		}
	}
	
	// which reads read something inwritten
	for readkey, txs := range txReads {
		for _, tx := range txs {
			if _, ok := txConflicts[tx]; !ok {
				txConflicts[tx] = make(map[int]bool)
			}
			// if this key is written then all of these conflict with all of those
			writetxs, ok := txWrites[readkey]
			if ok {
				// all the txs that write this key conflict with this tx
				for _, writetx := range writetxs {
					if _, ok := txConflicts[tx]; !ok {
						txConflicts[tx] = make(map[int]bool)
					}
					if writetx != tx {
						txConflicts[tx][writetx] = true
						// update the txConflicts of the writeTx too
						if _, ok := txConflicts[writetx]; !ok {
							txConflicts[writetx] = make(map[int]bool)
						}
						txConflicts[writetx][tx] = true
					}
				}
			} // this key isn't written by anything so it's a conflict free read
		}
	}

	conflictFreeTxs := make(map[int]bool)
	conflictTxs := make(map[int]bool)
	// which transactions are conflict free
	for i := 0; i < txidx; i++ {
		if _, ok := txConflicts[i]; !ok {
			conflictFreeTxs[i] = true
		} else {
			conflictTxs[i] = true
		}
	}
	
	log.Info("Txs", "conflict free", setToList(conflictFreeTxs), "conflicts", setToList(conflictTxs))

	// rank the conflicting keys from most conflicts to least
	// for every written to key, count the number of other transactions that need that key (writes and reads)
	keyConflicts := make(map[state.KeyKey]map[int]bool)
	for writekey, txs := range txWrites {
		for _, tx := range txs {
			if _, ok := keyConflicts[writekey]; !ok {
				keyConflicts[writekey] = make(map[int]bool)
			}
			keyConflicts[writekey][tx] = true
			othertxs, ok := txConflicts[tx]
			if ok {
				// if there are other conflicts add them too
				for othertx := range othertxs {
					keyConflicts[writekey][othertx] = true
				}
			}
		}
	}

	// num conflicts
	var numConflicts ConcurrentKeyValueList

	// 1. Populate the slice with KeyValuePair entries
	for key, value := range keyConflicts {
		numConflicts = append(numConflicts, ConcurrentKeyValuePair{
			Key:   key,
			Value: len(value),
		})
	}

	// 2. Sort the entire slice in descending order of Value
	sort.Sort(numConflicts)

	// 3. Return only the top 'limit' elements
	//if len(numConflicts) > 3 {
	//	log.Info("Most conflicts", "keys", numConflicts[:3])
	//} else {
	//	log.Info("Most conflicts", "keys", numConflicts)
	//}

	// reads of the excluded addrs
	//for excludedAddr := range ConcurrentExcludeAddrs {
	//	readCount := make(map[int]bool)
	//	for readkey, txs := range txWrites {
	//		if readkey.Addr().Cmp(excludedAddr) == 0 {
	//			for _, tx := range txs {
	//				readCount[tx] = true
	//			}
	//		}
	//	}
	//	log.Info("Reads to excluded", "addr", excludedAddr, "reads", len(readCount))
	//}

	return nil, nil, nil
}

// KeyValuePair is a helper struct to hold the string key and its integer value.
type ConcurrentKeyValuePair struct {
	Key   state.KeyKey
	Value int
}

// KeyValueList is a slice of KeyValuePair, used to implement the sort.Interface.
type ConcurrentKeyValueList []ConcurrentKeyValuePair

// --- Implementation of sort.Interface ---

func (l ConcurrentKeyValueList) Len() int {
	return len(l)
}

func (l ConcurrentKeyValueList) Swap(i, j int) {
	l[i], l[j] = l[j], l[i]
}

// Less reports whether the element at index i should sort before element j.
// We want descending order (largest value first), so we use >.
func (l ConcurrentKeyValueList) Less(i, j int) bool {
	return l[i].Value > l[j].Value
}


