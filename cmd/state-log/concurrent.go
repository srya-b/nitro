package main

import (
	"fmt"
	"sort"
	_"math"

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
		g, _ := BlockGraph(blockLogs)
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
		g, _ := BlockGraph(blockLogs)
		if g != nil {
			concurrent := g.Diameter() + 1
			sequential := g.NumVertices()
			percent := float64(sequential)/float64(concurrent)
			speedup = append(speedup, percent)
		}
	}
	FloatHistogramWriteFile(speedup, 0.25, "infinite-cores-speedup-histogram.csv")
}

func SimInfiniteCoresFromFile(dir string, accessFile string) {
	accessLists, _, err := ReadBlockAccesses(accessFile)
	if err != nil {
		log.Error("Couldn't read accesses from file", "file", accessFile)
		panic(err)
	}
	speedups := []float64{}
	diameters := []int{}
	for block, accesses := range accessLists {
		g := BlockGraphFromFile(block, accesses)
		if g == nil {
			panic("")
		}
		concurrent := g.Diameter() + 1
		sequential := g.NumVertices()
		percent := float64(sequential)/float64(concurrent)
		speedups = append(speedups, percent)
		diameters = append(diameters, concurrent)
	}
	HistogramWriteFile(diameters, 1, "infinite-cores-histogram.csv")
	FloatHistogramWriteFile(speedups, 0.25, "infinite-cores-speedup-histogram.csv")
}

func SimFiniteCores(dir string, K int, limit int) {
	logFiles := getLogFilesSorted(dir)
	diameters := []int{}
	for i, blockLogs := range logFiles {
		if i > limit {
			break
		}
		g, _ := BlockGraph(blockLogs)
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
		g, _ := BlockGraph(blockLogs)
		if g != nil {
			g.FiniteCores(K)
			concurrent := g.Diameter() + 1
			sequential := g.NumVertices()
			percent := float64(sequential)/float64(concurrent)
			speedup = append(speedup, percent)
		}
	}
	FloatHistogramWriteFile(speedup, 0.25, fmt.Sprintf("finite-%d-cores-speedup-histogram.csv", K))
}

func SimMultipleFiniteCores(dir string, krange []int, limit int) {
	logFiles := getLogFilesSorted(dir)
	blockGraphs := []*DependencyGraph{}

	for i, blockLogs := range logFiles {
		if i >= limit {
			break
		}
		g, _ := BlockGraph(blockLogs)
		if g != nil {
			blockGraphs = append(blockGraphs, g)
		}
	}

	for _, K := range krange {
		diameters := []int{}
		speedup := []float64{}
		for _, bgraph := range blockGraphs {
			g := bgraph.Copy()
			g.FiniteCores(K)
			concurrent := g.Diameter() + 1
			diameters = append(diameters, concurrent)
			sequential := g.NumVertices()
			percent := float64(sequential)/float64(concurrent)
			speedup = append(speedup, percent)
		}
		// do both of the graphs
		HistogramWriteFile(diameters, 1, fmt.Sprintf("finite-%d-cores-histogram.csv", K))
		FloatHistogramWriteFile(speedup, 0.25, fmt.Sprintf("finite-%d-cores-speedup-histogram.csv", K))
	}
	
}

func SimMultipleFiniteCoresFromFile(dir string, accessFile string, krange []int) {
	accessLists, _, err := ReadBlockAccesses(accessFile)
	if err != nil {
		log.Error("Couldn't read accesses from file", "file", accessFile)
		panic(err)
	}
	blockGraphs := []*DependencyGraph{}

	diameters := []int{}
	speedups := []float64{}
	for block, accesses := range accessLists {
		g := BlockGraphFromFile(block, accesses)
		blockGraphs = append(blockGraphs, g)
		concurrent := g.Diameter() + 1
		sequential := g.NumVertices()
		percent := float64(sequential)/float64(concurrent)
		speedups = append(speedups, percent)
		diameters = append(diameters, concurrent)
	}

	HistogramWriteFile(diameters, 1, "infinite-cores-histogram.csv")
	FloatHistogramWriteFile(speedups, 0.25, "infinite-cores-speedup-historam.csv")


	for _, K := range krange {
		diameters := []int{}
		speedup := []float64{}
		for _, bgraph := range blockGraphs {
			g := bgraph.Copy()
			g.FiniteCores(K)
			concurrent := g.Diameter() + 1
			diameters = append(diameters, concurrent)
			sequential := g.NumVertices()
			percent := float64(sequential)/float64(concurrent)
			speedup = append(speedup, percent)
		}
		// do both of the graphs
		HistogramWriteFile(diameters, 1, fmt.Sprintf("finite-%d-cores-histogram.csv", K))
		FloatHistogramWriteFile(speedup, 0.25, fmt.Sprintf("finite-%d-cores-speedup-histogram.csv", K))
	}
	
}

func SimMultipleGroupBlocks(dir string, accessFile string, krange []int, grouping int) {
	accessLists, _, err := ReadBlockAccesses(accessFile)
	if err != nil {
		log.Error("Couldn't read accesses from file", "file", accessFile)
		panic(err)
	}

	if len(accessLists) < grouping || len(accessLists) % grouping != 0  {
		panic("")
	}

	diameters := []int{}
	speedups := []float64{}
	newMap := groupMap(accessLists, grouping)

	blockGraphs := []*DependencyGraph{}
	for block, accesses := range newMap {
		g := BlockGraphFromFile(block, accesses)
		blockGraphs = append(blockGraphs, g)
		concurrent := g.Diameter() + 1
		sequential := g.NumVertices()
		percent := float64(sequential)/float64(concurrent)
		speedups = append(speedups, percent)
		diameters = append(diameters, concurrent)
	}
	HistogramWriteFile(diameters, 1, fmt.Sprintf("infinite-cores-%ds-histogram.csv", grouping))
	FloatHistogramWriteFile(speedups, 0.25, fmt.Sprintf("infinite-cores-speedup-%ds-historam.csv", grouping))

	for _, K := range krange {
		diameters := []int{}
		speedup := []float64{}
		for _, bgraph := range blockGraphs {
			g := bgraph.Copy()
			g.FiniteCores(K)
			concurrent := g.Diameter() + 1
			diameters = append(diameters, concurrent)
			sequential := g.NumVertices()
			percent := float64(sequential)/float64(concurrent)
			speedup = append(speedup, percent)
		}
		// do both of the graphs
		HistogramWriteFile(diameters, 1, fmt.Sprintf("finite-%d-cores-%ds-histogram.csv", K, grouping))
		FloatHistogramWriteFile(speedup, 0.25, fmt.Sprintf("finite-%d-cores-speedup-%ds-histogram.csv", K, grouping))
	}
}

var ConcurrentExcludeAddrs = map[common.Address]bool{
	common.HexToAddress("0xA4b05FffffFffFFFFfFFfffFfffFFfffFfFfFFFf"): true,
}

var Exclude = true

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

func BlockGraph(blockLogs []LogFile) (*DependencyGraph, int) {
	txWrites := make(map[state.KeyKey]map[int]bool)
	txReads := make(map[state.KeyKey]map[int]bool)
	conflicts := make(map[Conflict]bool)
	txidx := 0
	blockToReturn := 0
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
		
			if pre.Blockno != blockToReturn {
				if blockToReturn != 0 {
					log.Error("Block number changing twice!!!", "old", blockToReturn, "new", pre.Blockno)
					panic("")
				}
				blockToReturn = pre.Blockno
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
						txReads[kk] = make(map[int]bool)
					}
					//txReads[kk] = append(txReads[kk], txidx)
					txReads[kk][txidx] = true
					
					// if this read is of a slot that was written before then this is a conflict
					writeTxs, exists := txWrites[kk]
					if exists {
						for wtx, _ := range writeTxs {
							if txidx != wtx {
								//conflicts = append(conflicts, Conflict{txidx, wtx})	
								conflicts[Conflict{txidx, wtx}] = true
							}
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

					// if this slot was written before then this is a conflict as well

					writeTxs, ok := txWrites[kk]
					if ok {
						for wtx, _ := range writeTxs {
							if txidx != wtx {
								//conflicts = append(conflicts, Conflict{txidx, wtx})
								conflicts[Conflict{txidx, wtx}] = true
							}
						}
					} else {
						//txWrites[kk] = []int{}
						txWrites[kk] = make(map[int]bool)
					}
					//txWrites[kk] = append(txWrites[kk], txidx)
					txWrites[kk][txidx] = true
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
		//for _, cn := range conflicts {
		for cn, _ := range conflicts {
			err := graph.AddEdge(cn.tx1, cn.tx2)
			if err != nil {
				log.Error("Failed to add an edge to the graph", "err", err, "tx1", cn.tx1, "tx2", cn.tx2)
				graph.Display("Conflicts")
				panic("")
			}
		}
		log.Info("Block", "number", blockLogs[0].Blockno, "txid", txidx, "conflicts", len(conflicts), "graph", graph.Diameter(), "vertices", graph.NumVertices())
		//graph.Display()
		//return graph.Diameter()
		return &graph, blockToReturn
	}
	return nil, blockToReturn
}

func BlockGraphFromFile(blockno int, accesses [][]state.KeyKey) *DependencyGraph {
	conflicts := make(map[Conflict]bool)
	txWrites := make(map[state.KeyKey]map[int]bool)
	txid := 0
	for i := 0; i < len(accesses) - 1; i += 2 {
		readAccesses := accesses[i]
		writeAccesses := accesses[i+1]
		
		for _, kk := range readAccesses {
			if _, ok := ConcurrentExcludeAddrs[kk.Addr()]; ok && Exclude {
				continue
			}

			// if there was a previous write to this, there is a conflict
			writeTxs, exists := txWrites[kk]
			if exists {
				for wtx, _ := range writeTxs {
					if txid != wtx {
						conflicts[Conflict{txid, wtx}] = true
					}
				}
			}
		}		 

		for _, kk := range writeAccesses {
			if _, ok := ConcurrentExcludeAddrs[kk.Addr()]; ok && Exclude {
				continue
			}

			// if there was a previous write to this it's also a conficts
			writeTxs, exists := txWrites[kk]
			if exists {
				for wtx, _ := range writeTxs {
					if txid != wtx {
						conflicts[Conflict{txid, wtx}] = true
					}
				}
			} else {
				// if this was never written before, add it to the map
				txWrites[kk] = make(map[int]bool)
			}
			// record that this transaction also writes to this
			txWrites[kk][txid] = true
		}
		txid++
	}

	graph := NewDependencyGraph(txid, blockno)
	if len(conflicts) > 0 {
		log.Info("Conflicts", "l", conflicts)
	}
	for cn, _ := range conflicts {
		err := graph.AddEdge(cn.tx1, cn.tx2)
		if err != nil {
			log.Error("Failed to add an edge to the graph", "err", err, "tx1", cn.tx1, "tx2", cn.tx2)
			graph.Display("Conflicts")
			panic("")
		}
	}
	log.Info("Block", "number", blockno, "txid", len(accesses)/2, "conflicts", len(conflicts), "graph", graph.Diameter(), "vertices", graph.NumVertices())
	return &graph
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

// ---- testing functions -------

func CompareSpecificBlock(dir string, accessFile string, limit int, target int) {
	log.Info("Check target block", "n", target)
	logFiles := getLogFilesSorted(dir)
	var targetLiveGraph *DependencyGraph
	lastBlockNo := 0
	for i, blockLogs := range logFiles {
		if i >= limit {
			break
		}
		g, b, ok := BlockGraphTargetBlock(blockLogs, target)
		if !ok {
			continue
		}
		
		if g != nil {
			targetLiveGraph = g
			lastBlockNo = b
		} 
		break
	}
	
	accessLists, firstBlock, err := ReadBlockAccesses(accessFile)
	if err != nil {
		log.Error("Couldn't read accesses from file", "file", accessFile)
		panic(err)
	}
	
	var targetFileGraph *DependencyGraph

	for i := 0; i < len(accessLists); i++ {
		if firstBlock+i == target {
			accesses, ok := accessLists[firstBlock+i]
			if !ok {
				log.Debug("Skipping block", "n", firstBlock+i)
				panic("Skipping target block")
			}
			g := BlockGraphFromFile(firstBlock+i, accesses)
			targetFileGraph = g
			if firstBlock+i == lastBlockNo {
				break
			}
		}
	}
	
	if targetLiveGraph == nil {
		log.Error("Live gave no graph for block")
	}
	if targetFileGraph == nil {
		log.Error("File gave no graph for block")
	}
	if targetLiveGraph == nil || targetFileGraph == nil {
		panic("nil graph")
	}

	sameVertices, selfNotOther, otherNotSelf := targetLiveGraph.HasSameVertices(targetFileGraph)
	areEqual, edgesInSelfNotOther := targetLiveGraph.IsEqual(targetFileGraph)
	if !areEqual {
		log.Error("Graphs aren't equal", "diff", edgesInSelfNotOther)
	} 
	if !sameVertices {
		log.Error("Different vertices", "selfNotOther", selfNotOther, "otherNotSelf", otherNotSelf)
	}
	if !sameVertices || !areEqual {
		panic("")
	}
}

func CheckSameGraphFileAndLive(dir string, accessFile string, limit int) {
	logFiles := getLogFilesSorted(dir)
	liveBlockGraphs := make(map[int]*DependencyGraph)
	lastBlockNo := 0
	for i, blockLogs := range logFiles {
		if i >= limit {
			break
		}
		g, b := BlockGraph(blockLogs)
		if g != nil {
			//blockGraphs = append(blockGraphs, g)
			liveBlockGraphs[b] = g
			lastBlockNo = b
		}
	}

	accessLists, firstBlock, err := ReadBlockAccesses(accessFile)
	if err != nil {
		log.Error("Couldn't read accesses from file", "file", accessFile)
		panic(err)
	}
	//fileBlockGraphs := []*DependencyGraph{}
	fileBlockGraphs := make(map[int]*DependencyGraph)

	for i := 0; i < len(accessLists); i++ {
		accesses, ok := accessLists[firstBlock+i]
		if !ok {
			log.Debug("Skipping block", "n", firstBlock+i)
			continue
		}
		g := BlockGraphFromFile(firstBlock+i, accesses)
		//fileBlockGraphs = append(fileBlockGraphs, g)
		fileBlockGraphs[firstBlock+i] = g
		if firstBlock+i == lastBlockNo {
			break
		}
	}

	if len(liveBlockGraphs) != len(fileBlockGraphs) {
		log.Error("Different number of graphs", "live", len(liveBlockGraphs), "file", len(fileBlockGraphs))
	}

	for b, liveG := range liveBlockGraphs {
		fileG, exists := fileBlockGraphs[b]
		if !exists {
			log.Error("live blockgraph exists but file doesn't", "block", b)
		}

		// check they are the same
		sameVertices, selfNotOther, otherNotSelf := liveG.HasSameVertices(fileG)
		areEqual, edgesInSelfNotOther := liveG.IsEqual(fileG)
		if !areEqual {
			log.Error("Graphs aren't equal", "block", b, "diff", edgesInSelfNotOther)
		} 
		if !sameVertices {
			log.Error("Different vertices", "block", b, "selfNotOther", selfNotOther, "otherNotSelf", otherNotSelf)
		}
		if !sameVertices || !areEqual {
			panic("")
		}
	}	
}

func BlockGraphTargetBlock(blockLogs []LogFile, target int) (*DependencyGraph, int, bool) {
	txWrites := make(map[state.KeyKey]map[int]bool)
	txReads := make(map[state.KeyKey]map[int]bool)
	conflicts := make(map[Conflict]bool)
	txidx := 0
	blockToReturn := 0
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

			if pre.Blockno != target {
				return nil, blockToReturn, false
			}		
			log.Info("Blocklogs", "l", len(blockLogs))

			if pre.Blockno != blockToReturn {
				if blockToReturn != 0 {
					log.Error("Block number changing twice!!!", "old", blockToReturn, "new", pre.Blockno)
					panic("")
				}
				blockToReturn = pre.Blockno
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
						txReads[kk] = make(map[int]bool)
					}
					txReads[kk][txidx] = true
					
					// if this read is of a slot that was written before then this is a conflict
					writeTxs, exists := txWrites[kk]
					if exists {
						for wtx, _ := range writeTxs {
							if txidx != wtx {
								conflicts[Conflict{txidx, wtx}] = true
							}
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

					// if this slot was written before then this is a conflict as well

					writeTxs, ok := txWrites[kk]
					if ok {
						for wtx, _ := range writeTxs {
							if txidx != wtx {
								conflicts[Conflict{txidx, wtx}] = true
							}
						}
					} else {
						txWrites[kk] = make(map[int]bool)
					}
					txWrites[kk][txidx] = true
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
		//for _, cn := range conflicts {
		for cn, _ := range conflicts {
			err := graph.AddEdge(cn.tx1, cn.tx2)
			if err != nil {
				log.Error("Failed to add an edge to the graph", "err", err, "tx1", cn.tx1, "tx2", cn.tx2)
				graph.Display("Conflicts")
				panic("")
			}
		}
		log.Info("Block", "number", blockLogs[0].Blockno, "txid", txidx, "conflicts", len(conflicts), "graph", graph.Diameter(), "vertices", graph.NumVertices())
		//graph.Display()
		//return graph.Diameter()
		return &graph, blockToReturn, true
	}
	return nil, blockToReturn, false
}
