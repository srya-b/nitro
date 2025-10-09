package main

import (
	"fmt"
	"sort"
	"math"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/core/state"
)


func ConcurrentRun(dir string) {
	logPairs := validatedLogs(dir, 100)
	BlockGraphs(logPairs)
}

func SimInfiniteCores(dir string, limit int) {
	logFiles := getLogFilesSorted(dir)
	diameters := []int{}
	for i, blockLogs := range logFiles {
		if i > limit {
			break
		}
		g := BlockGraph(blockLogs)
		if g != nil {
			diameters = append(diameters, g.Diameter())
		}
	}
	HistogramWriteFile(diameters, 1, "infinite-cores-histogram.csv")
}

func SimInfiniteCoresSpeedup(dir string, limit int) {
	logFiles := getLogFilesSorted(dir)
	speedup := []float64{}
	for i, blockLogs := range logFiles {
		if i > limit {
			break
		}
		
		// The diameter of the dependency graph + 1 is the time for the parallel
		// execution.  The number of vertices is the execution time sequentially.
		g := BlockGraph(blockLogs)
		if g != nil {
			concurrent := g.Diameter() + 1
			sequential := g.NumVertices()
		 	percent := float64(100) * math.Abs((float64(concurrent)-float64(sequential))/float64(sequential))
			speedup = append(speedup, percent)
			//diameters = append(diameters, g.Diameter())
		}
	}
	FloatHistogramWriteFile(speedup, 2.0, "infinite-cores-speedup-histogram.csv")
}

func SimFiniteCores(dir string, K int, limit int) {
	logFiles := getLogFilesSorted(dir)
	diameters := []int{}
	for i, blockLogs := range logFiles {
		if i > limit {
			break
		}
		g := BlockGraph(blockLogs)
		if g != nil {
			g.FiniteCores(K)
			diameters = append(diameters, g.Diameter()+1)
		}
	}
	HistogramWriteFile(diameters, 1, fmt.Sprintf("finite-%d-cores-histogram.csv", K))
}

func SimFiniteCoresSpeedup(dir string, K int, limit int) {
	logFiles := getLogFilesSorted(dir)
	speedup := []float64{}
	for i, blockLogs := range logFiles {
		if i > limit {
			break
		}
		
		// The concurrent runtime is the diameter of the modified graph with artificial
		// dependencies created.  The sequential time is the ceiling( # vertices / K )
		g := BlockGraph(blockLogs)
		if g != nil {
			g.FiniteCores(K)
			concurrent := g.Diameter() + 1
			//sequential := math.Ceil(float64(g.NumVertices())/float64(K))
			// NOTE: it doesn't make sense for the sequential to be (# vertices)/K because you
			// Can't run any in parallel since you don't know whether there are conflicts
			// DUHHH
			sequential := g.NumVertices()
		 	percent := float64(100) * math.Abs((float64(concurrent)-float64(sequential))/float64(sequential))
			if percent >= float64(100) {
				log.Debug("concurrency slowed it down?", "concurrent", concurrent, "sequential", sequential)
				panic("")
			}
			speedup = append(speedup, percent)
			//diameters = append(diameters, g.Diameter())
		}
	}
	FloatHistogramWriteFile(speedup, 2.0, fmt.Sprintf("finite-%d-cores-speedup-histogram.csv", K))
}

func SimMultipleFiniteCores(dir string, krange []int, limit int) {
	logFiles := getLogFilesSorted(dir)
	blockGraphs := []*DependencyGraph{}

	for i, blockLogs := range logFiles {
		if i >= limit {
			break
		}
		g := BlockGraph(blockLogs)
		if g != nil {
			blockGraphs = append(blockGraphs, g)
		}
	}

	for _, K := range krange {
		diameters := []int{}
		speedup := []float64{}
		for _, bgraph := range blockGraphs {
			g := bgraph.Copy()
			// just the diameters
			g.FiniteCores(K)
			concurrent := g.Diameter() + 1
			diameters = append(diameters, concurrent)
			// the speedup
			//sequential := math.Ceil(float64(g.NumVertices())/float64(K))
			// NOTE: it doesn't make sense for the sequential to be (# vertices)/K because you
			// Can't run any in parallel since you don't know whether there are conflicts
			// DUHHH
			sequential := g.NumVertices()
			percent := float64(100) * math.Abs((float64(concurrent)-float64(sequential))/float64(sequential))
			if percent >= float64(100) {
				log.Debug("concurrency slowed it down?", "concurrent", concurrent, "sequential", sequential)
				panic("")
			}
			speedup = append(speedup, percent)
		}
		// do both of the graphs
		HistogramWriteFile(diameters, 1, fmt.Sprintf("finite-%d-cores-histogram.csv", K))
		FloatHistogramWriteFile(speedup, 2.0, fmt.Sprintf("finite-%d-cores-speedup-histogram.csv", K))
	}
	
}



var ConcurrentExcludeAddrs = map[common.Address]bool{
	common.HexToAddress("0xA4b05FffffFffFFFFfFFfffFfffFFfffFfFfFFFf"): true,
}

var Exclude = false

// DEPRECATED BECAUSE IT DOESN'T ACTUALLY WORK.
func BlockGraphs(pairs [][]LogPair) {
	// loop over the blocks
	for _, logPairs := range pairs {
		//txReads := make(map[state.KeyKey][]int)
		txWrites := make(map[state.KeyKey][]int)
		txidx := 0
		conflicts := []Conflict{}
		// over all the logs generated in this block
		if len(logPairs) == 0 {
			continue
		}
		for _, pair := range logPairs {
			preObj := pair.PreObj
			ejournals := state.JournalsToExported(preObj.Journals)
			// this is a loop over txs basically	
			for _, journal := range ejournals {
				// gather all the reads and figure out the conflicts
				reads := GetReadButNotWrite(journal)
				for kk := range reads {
					if _, ok := ConcurrentExcludeAddrs[kk.Addr()]; ok && Exclude {
						// skip this addr and see what happens
						continue
					}

					// If previous transactions have written to this then there
					// is a conflict.
					writeTxs, exists := txWrites[kk]
					if exists {
						for _, wtx := range writeTxs {
							// there is a dependency here
							if wtx > txidx {
								panic("Previous write tx is more than current")
							}
							//graph.AddEdge(txidx, wtx)	
							conflicts = append(conflicts, Conflict{txidx, wtx})
						}
					}
					//readTxs, exists := txReads[kk]
					//if exists {
					//	for _, rtx := range readTxs {
					//		if rtx > txidx {
					//			panic("Previous read tx is more than current")
					//		}
					//		conflicts = append(conflicts, Conflict{txidx, rtx})
					//	}
					//}
					//_, ok := txReads[kk]
					//if !ok {
					//	txReads[kk] = []int{}
					//}
					//txReads[kk] = append(txReads[kk], txidx)
				}

				// log the things it writes
				written := GetWrittenKeys(journal)
				//log.Info("Read/Write", "reads", len(reads), "writes", len(written))
				for kk := range written {
					if _, ok := ConcurrentExcludeAddrs[kk.Addr()]; ok && Exclude {
						// skip this addr and see what happens
						continue
					}
					_, ok := txWrites[kk]
					if !ok {
						txWrites[kk] = []int{}
					}
					txWrites[kk] = append(txWrites[kk], txidx)
				}
				txidx++
			}
		}
		// is it nil
		graph := NewDependencyGraph(txidx, logPairs[0].BlockNo)
		for _, cn := range conflicts {
			graph.AddEdge(cn.tx1, cn.tx2)
		}
		log.Info("Block", "number", logPairs[0].BlockNo, "txid", txidx, "conflicts", len(conflicts), "graph", graph.Diameter())
		if graph.Diameter() > 1 {
			break
		}
		//graph.Display()
	}
}

// Given a the log files for a block, what transactions conflict with each other,
// and what are the most common conflicting storage slots returns list of
// transactions have no conflicts returns the pairs of tranactions that conflict
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
	if len(numConflicts) > 3 {
		log.Info("Most conflicts", "keys", numConflicts[:3])
	} else {
		log.Info("Most conflicts", "keys", numConflicts)
	}

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

func BlockGraph(blockLogs []LogFile) *DependencyGraph {
	txWrites := make(map[state.KeyKey][]int)
	txReads := make(map[state.KeyKey][]int)
	conflicts := []Conflict{}
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
				// log the things
				reads := GetReadButNotWrite(journal)
				for kk := range reads {
					if _, ok := ConcurrentExcludeAddrs[kk.Addr()]; ok && Exclude {
						// skip this addr and see what happens
						continue
					}
					_, ok := txReads[kk]
					if !ok {
						txReads[kk] = []int{}
					}
					txReads[kk] = append(txReads[kk], txidx)

					writeTxs, exists := txWrites[kk]
					if exists {
						for _, wtx := range writeTxs {
							conflicts = append(conflicts, Conflict{txidx, wtx})	
						}
					}
				}
				// log the things it writes
				written := GetWrittenKeys(journal)
				for kk := range written {
					if _, ok := ConcurrentExcludeAddrs[kk.Addr()]; ok && Exclude {
						// skip this addr and see what happens
						continue
					}
					_, ok := txWrites[kk]
					if !ok {
						txWrites[kk] = []int{}
					}
					txWrites[kk] = append(txWrites[kk], txidx)
				}
				txidx++
			}
		}
	}
	if txidx > 0 {
		//log.Info("Conflicts", "block", blockLogs[0].Blockno, "conflicts", len(conflicts))
		graph := NewDependencyGraph(txidx, blockLogs[0].Blockno)
		if len(conflicts) > 0 {
			log.Info("Conflicts", "l", conflicts)	
		}
		for _, cn := range conflicts {
			graph.AddEdge(cn.tx1, cn.tx2)
		}
		log.Info("Block", "number", blockLogs[0].Blockno, "txid", txidx, "conflicts", len(conflicts), "graph", graph.Diameter(), "vertices", graph.NumVertices())
		//graph.Display()
		//return graph.Diameter()
		return &graph
	}
	return nil
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
