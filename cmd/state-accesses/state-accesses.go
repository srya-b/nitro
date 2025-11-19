package main

import (
	"os"
	"fmt"
	"math"
	"sort"
	"flag"
	"math/big"
	_"strconv"

	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/common"
	_"github.com/ethereum/go-ethereum/core/types"
)

// ---------- additional parameters ----------
var accessFlags = AccessOpcode | AccessCode
var krange = []int{2, 4, 8, 16}
// -------------------------------------------

func main() {
	os.Exit(mainImpl())
}

func mainImpl() int {
	log.SetDefault(log.NewLogger(log.NewTerminalHandlerWithLevel(os.Stderr, log.LevelDebug, true)))

	batchesPtr := flag.Int("batches", 1, "The number of batches to process.")
	debugPtr := flag.Bool("debug", false, "Enable debug mode.")
	limitPtr := flag.Int("limit", math.MaxInt, "Limit the number of items to process (default: no limit).")
	listConflictsPtr := flag.Bool("list-conflicts", false, "List accesses that conflict across ALL transactions in the block.")
	speedupPtr := flag.String("speedups", "", "Write the speedups per block, per core number, to a csv file")

	flag.Usage = func() {
		fmt.Fprintf(os.Stderr, "Usage: %s [options] <data_dir> <output_dir>\n", os.Args[0])
		fmt.Fprintf(os.Stderr, "Options:\n")
		flag.PrintDefaults()
	}

	flag.Parse()

	positionalArgs := flag.Args()

	// 3. Check if we have the correct number of required arguments
	if len(positionalArgs) < 2 {
		fmt.Println("Error: Missing required data_dir and output_dir arguments.")
		flag.Usage() // Print the custom usage message
		return 1
	}

	//if *limitPtr != math.MaxInt && *batchesPtr > 1 {
	//	fmt.Println("Error: can't set a limit AND a number of batches. I'm not that sophisticated yet.")
	//	return 1
	//}

	datadir := positionalArgs[0]
	destdir := positionalArgs[1]

	fmt.Println("--- Program starting with configuration ---")
	fmt.Printf("Data Directory:   %s\n", datadir)
	fmt.Printf("Output Directory: %s\n", destdir)
	fmt.Printf("Batches:          %d\n", *batchesPtr)
	fmt.Printf("Debug Mode:       %t\n", *debugPtr)
	fmt.Printf("List conflicts:   %t\n", *listConflictsPtr)

	limitVal := "Not set"
	if *limitPtr != math.MaxInt {
		limitVal = fmt.Sprintf("%d", *limitPtr)
	}
	fmt.Printf("Limit:            %s\n", limitVal)
	fmt.Println("-------------------------------------------")

	limit := *limitPtr
	debug := *debugPtr
	batches := *batchesPtr
	listConflicts := *listConflictsPtr

	sortedFiles, err := getSortedTraceFiles(datadir)
	if err != nil {
		log.Error("Failed", "err", err)
		return 1
	}
	
	if limit != math.MaxInt {
		sortedFiles = sortedFiles[:limit]
	}

	log.Info("Block access data", "first", sortedFiles[0].num, "last", sortedFiles[len(sortedFiles)-1].num)

	if *speedupPtr != "" {
		return mainSpeedups(sortedFiles, destdir, *speedupPtr, batches, debug, listConflicts)
	}

	if batches > 1 {
		return mainBatched(sortedFiles, destdir, batches, debug, listConflicts)
	}	


	// --------------- process everything in one go -------------
	// if the data is too big, then you want to batch or the os will
	// kill the proces
	blockTraces := make([]*BlockTrace, 0, len(sortedFiles))
	actuallyUsed := 0
	for i, file := range sortedFiles {
		if i >= limit {
			break
		}
		trace, err := BlockTraceFromFile(file) 
		if err != nil {
			log.Error("Failed to get block trace", "err", err)
			return 1
		}

		blockTraces = append(blockTraces, trace)
		if actuallyUsed % 10000 == 0 {
			log.Info("Processed", "used", actuallyUsed)
		}
		actuallyUsed++
	}

	// the output directory of all these files is determined by the access flags and limit
	outdir := fmt.Sprintf("%s/concurrent-%d-%s", destdir, actuallyUsed, FormatAccessFlags(accessFlags))

	if err := os.MkdirAll(outdir, 0755); err != nil {
		log.Error("Couldn't create output directory for this run", "dir", outdir)
		return 1
	}	
	
	log.Info("Outdir", "outdir", outdir)

	blockSpeedups := SimMultipleFiniteCores(blockTraces, actuallyUsed, krange, outdir, accessFlags, debug, listConflicts)

	speedupsFn := fmt.Sprintf("%s/block-speedups.csv", outdir)
	log.Info("Writing speedups to file", "file", speedupsFn, "num speedups", len(blockSpeedups))
	if err := writeSpeedupsToFile(blockSpeedups, speedupsFn); err != nil {
		fmt.Printf("Error writing block speedups to file: %v", err)
		return 1
	}	
	return 0
}

type BlockSpeedup struct {
	BlockNumber	 	*big.Int
	Sequential	 	uint64
	Equivalent		map[int]uint64
}

func SimMultipleFiniteCores(blockTraces []*BlockTrace, limit int, krange []int, outdir string, filterFlags AccessType, debug bool, listConflicts bool) []*BlockSpeedup {
	blockGraphs := make([]*WeightedVertexGraph, 0, len(blockTraces))
	//diameters := []int{}
	//speedups := []float64{}
	//totalGas := []uint64{}
	//equivalentGas := []uint64{}
	gasSpeedups := make([]float64, 0, len(blockTraces))
	
	blockSpeedups := make([]*BlockSpeedup, 0, len(blockTraces))
	for _, trace := range blockTraces {
		g := BlockGraph(trace, filterFlags, listConflicts)
		blockGraphs = append(blockGraphs, g)
		//concurrent := g.Diameter() + 1
		//sequential := g.NumVertices()
		//concurrent := g.MaxWeightedVertexPath()
		concurrent := g.HeaviestPath()
		sequential := g.TotalVertexWeight()
		//percent := float64(sequential)/float64(concurrent)
		//speedups = append(speedups, percent)
		//diameters = append(diameters, concurrent)
		//totalGas = append(totalGas, sequential)
		//equivalentGas = append(equivalentGas, concurrent)
		var speedup float64
		if sequential == 0 {
			speedup = float64(0)
		} else {
			speedup = float64(sequential)/float64(concurrent)
		}
		gasSpeedups = append(gasSpeedups, speedup)
		blockSpeedup := &BlockSpeedup{
			BlockNumber:	trace.BlockNumber,
			Sequential:		sequential,
			Equivalent:		map[int]uint64{
								-1: concurrent,
							},
		}	
		blockSpeedups = append(blockSpeedups, blockSpeedup)
	}	


	if !debug {
		//HistogramWriteFile(diameters, 1, fmt.Sprintf("%s/infinite-cores-histogram.csv", outdir))
		FloatHistogramWriteFile(gasSpeedups, 0.25, fmt.Sprintf("%s/infinite-cores-speedup-histogram.csv", outdir))
	}


	// finite cores for each number of cores K in krange
	for _, K := range krange {
		//totalGas := []uint64{}
		//equivalentGas := []uint64{}
		gasSpeedups := []float64{}
		for i, bgraph := range blockGraphs {
			g := bgraph.Copy()
			g.FiniteCores(K)
			//concurrent := g.MaxWeightedVertexPath()
			concurrent := g.HeaviestPath()
			sequential := g.TotalVertexWeight()
			//totalGas = append(totalGas, sequential)
			//equivalentGas = append(equivalentGas, concurrent)
			var speedup float64
			if sequential == 0 {
				speedup = float64(0)
			} else {
				speedup = float64(sequential)/float64(concurrent)
			}
			gasSpeedups = append(gasSpeedups, speedup)
			blockSpeedups[i].Equivalent[K] = concurrent
			if debug {
				log.Info("Speedup", "K", K, "sequential", sequential, "concurrentGas", concurrent, "speedup", speedup)
			}
		}
		
		if !debug {
			//HistogramWriteFile(diameters, 1, fmt.Sprintf("%s/finite-%d-cores-histogram.csv", outdir, K))
			FloatHistogramWriteFile(gasSpeedups, 0.25, fmt.Sprintf("%s/finite-%d-cores-speedup-histogram.csv", outdir, K))
		}
	}

	return blockSpeedups
}

func mainSpeedups(logs []fileWithNum, destdir string, outfile string, batches int, debug bool, listConflicts bool) int {
	return 0
	//log.Info("Executing mainSpeedups.")

	//batchedSortedFiles := splitSliceIntoNParts(logs, batches)
	//log.Info("Split into batches")
	//for _, batch := range batchedSortedFiles {
	//	fmt.Printf("Batch: %d - %d = %d", batch[0].num, batch[len(batch)-1].num, batch[len(batch)-1].num - batch[0].num)
	//}
	//
	//blockSpeedups := make([]BlockSpeedup, 0, len(logs))
	//totalTracesUsed := 0

	//// go through them in batches, eventually blockTraces :: []*BlockTrace is cleared
	//// and that should free program memory
	//for batchno, sortedFiles := range batchedSortedFiles {
	//	log.Info(fmt.Sprintf("Processing files for batch %d", batchno))
	//	blockTraces := make([]*BlockTrace, 0, len(sortedFiles))
	//	actuallyUsed := 0
	//
	//	// create block traces for the txs in the block in this batch
	//	// of log files
	//	for _, file := range sortedFiles {
	//		trace, err := BlockTraceFromFile(file) 
	//		if err != nil {
	//			log.Error("Failed to get block trace", "err", err)
	//			return 1
	//		}

	//		blockTraces = append(blockTraces, trace)
	//		if actuallyUsed % 10000 == 0 && actuallyUsed > 0 {
	//			log.Info("Processed", "used", actuallyUsed)
	//		}
	//		actuallyUsed++
	//		totalTracesUsed++
	//	}

	//	// returns the diameter and speedup instograms for each number of cores and infinite cores
	//	// diameters :: map[int]map[int]int and is indexed by k in {-1, 2, 4, 8, 16} and -1 is the key
	//	// for the infinite cores histogram (analogous for speedups :: map[int]map[float64]int
	//	speedups := SimMultipleFiniteCoresSpeedups(blockTraces, krange, debug, accessFlags, listConflicts)

	//	// merge this batches histograms with all previous batches
	//	log.Info(fmt.Sprintf("Accumulating diameter data for batch %d", batchno))
	//	for k, h := range diameters {
	//		if hist, exists := kDiameterHistograms[k]; exists {
	//			mergeHistograms(hist, h)
	//		} else {
	//			kDiameterHistograms[k] = h
	//		}
	//	}

	//	log.Info(fmt.Sprintf("Accumulating speedup data for batch %d", batchno))
	//	for k, h := range speedups {
	//		if hist, exists := kSpeedupHistograms[k]; exists {
	//			mergeFloatHistograms(hist, h)
	//		} else {
	//			kSpeedupHistograms[k] = h
	//		}
	//	}
	//}
}

// identical to the regular version but this just returns the histogram rather than doing any plotting
func SimMultipleFiniteCoresSpeedups(blockTraces []*BlockTrace, krange []int, debug bool, filterFlags AccessType, listConflicts bool) []BlockSpeedup {
	return nil
	//blockGraphs := make([]*WeightedVertexGraph, 0, len(blockTraces))
	//diameters := []int{}
	//speedups := []float64{}

	//// finite cores for each number of cores K in krange
	//kDiameterMap := make(map[int]IntHistogram)
	//kSpeedupMap := make(map[int]FloatHistogram)

	//totalGas := []int{}
	//gasSpeedups := []float64{}
	//log.Info(fmt.Sprintf("Processing %d batches for ininite cores.", len(blockTraces)))
	//for _, trace := range blockTraces {
	//	g := BlockGraph(trace, filterFlags, listConflicts)
	//	blockGraphs = append(blockGraphs, g)
	//	concurrent := g.Diameter() + 1
	//	sequential := g.NumVertices()
	//	percent := float64(sequential)/float64(concurrent)
	//	speedups = append(speedups, percent)
	//	diameters = append(diameters, concurrent)
	//	
	//	sequentialGas := int(g.TotalVertexWeight())
	//	concurrentGas := int(g.MaxWeightedVertexPath())
	//	percent = float64(sequentialGas)/float64(concurrentGas)
	//	totalGas = append(totalGas, sequentialGas)
	//	gasSpeedups = append(gasSpeedups, percent)
	//}	


	//log.Info("Saving infinite cores data.")
	//infiniteDiametersHist := createHistogram(diameters, 1)
	//infiniteSpeedupHist := createFloatHistogram(speedups, 0.25)
	//kDiameterMap[-1] = infiniteDiametersHist
	//kSpeedupMap[-1] = infiniteSpeedupHist
	////HistogramWriteFile(diameters, 1, fmt.Sprintf("%s/infinite-cores-histogram.csv", outdir))
	////FloatHistogramWriteFile(speedups, 0.25, fmt.Sprintf("%s/infinite-cores-speedup-historam.csv", outdir))

	//for _, K := range krange {
	//	diameters := []int{}
	//	speedups := []float64{}

	//	totalGas := []int{}
	//	gasSpeedups := []float64{}
	//	log.Info(fmt.Sprintf("Processing %d batches for %d cores.", len(blockTraces), K))
	//	for _, bgraph := range blockGraphs {
	//		g := bgraph.Copy()
	//		g.FiniteCores(K)
	//		concurrent := g.Diameter() + 1
	//		sequential := g.NumVertices()
	//		percent := float64(sequential)/float64(concurrent)
	//		speedups = append(speedups, percent)
	//		diameters = append(diameters, concurrent)
	//		
	//		sequentialGas := int(g.TotalVertexWeight())
	//		concurrentGas := int(g.MaxWeightedVertexPath())
	//		percent = float64(sequentialGas)/float64(concurrentGas)
	//		totalGas = append(totalGas, sequentialGas)
	//		gasSpeedups = append(gasSpeedups, percent)
	//		if debug {
	//			log.Info("Speedup", "K", K, "sequential", sequentialGas, "concurrentGas", concurrentGas)
	//		}
	//	}
	//	

	//	log.Info("Saving finite cores data.")
	//	diameterHist := createHistogram(diameters, 1)
	//	speedupHist := createFloatHistogram(speedups, 0.25)
	//	kDiameterMap[K] = diameterHist
	//	kSpeedupMap[K] = speedupHist
	//	//HistogramWriteFile(diameters, 1, fmt.Sprintf("%s/finite-%d-cores-histogram.csv", outdir, K))
	//	//FloatHistogramWriteFile(speedups, 0.25, fmt.Sprintf("%s/finite-%d-cores-speedup-histogram.csv", outdir, K))
	//}

	//return kDiameterMap, kSpeedupMap
}

type UintHistogram map[int]int
type FloatHistogram map[float64]int

func mainBatched(logs []fileWithNum, destdir string, batches int, debug bool, listConflicts bool) int {
	log.Info("Executing in batches.")

	batchedSortedFiles := splitSliceIntoNParts(logs, batches)
	log.Info("Split into batches")
	for _, batch := range batchedSortedFiles {
		fmt.Printf("Batch: %d - %d = %d", batch[0].num, batch[len(batch)-1].num, batch[len(batch)-1].num - batch[0].num)
	}
	
	kSpeedupHistograms := make(map[int]map[float64]int)
	//blockSpeedups := make([]*BlockSpeedup, 0, len(logs))
	blockSpeedups := []*BlockSpeedup{}
	totalTracesUsed := 0
	
	// go through them in batches, eventually blockTraces :: []*BlockTrace is cleared
	// and that should free program memory
	for batchno, sortedFiles := range batchedSortedFiles {
		log.Info(fmt.Sprintf("Processing files for batch %d", batchno))
		blockTraces := make([]*BlockTrace, 0, len(sortedFiles))
		actuallyUsed := 0
	
		// create block traces for the txs in the block in this batch
		// of log files
		for _, file := range sortedFiles {
			trace, err := BlockTraceFromFile(file) 
			if err != nil {
				log.Error("Failed to get block trace", "err", err)
				return 1
			}

			blockTraces = append(blockTraces, trace)
			if actuallyUsed % 10000 == 0 && actuallyUsed > 0 {
				log.Info("Processed", "used", actuallyUsed)
			}
			actuallyUsed++
			totalTracesUsed++
		}

		// returns the diameter and speedup instograms for each number of cores and infinite cores
		// diameters :: map[int]map[int]int and is indexed by k in {-1, 2, 4, 8, 16} and -1 is the key
		// for the infinite cores histogram (analogous for speedups :: map[int]map[float64]int
		batchGasSpeedups, batchBlockSpeedups := SimMultipleFiniteCoresBatched(blockTraces, krange, debug, accessFlags, listConflicts)

		// merge this batches histograms with all previous batches
		log.Info(fmt.Sprintf("Accumulating speedup data for batch %d", batchno))
		for k, h := range batchGasSpeedups {
			if hist, exists := kSpeedupHistograms[k]; exists {
				mergeFloatHistograms(hist, h)
			} else {
				kSpeedupHistograms[k] = h
			}
		}

		// add to blockSpeedups
		for _, bs := range batchBlockSpeedups {
			blockSpeedups = append(blockSpeedups, bs)
		}

		if len(blockSpeedups) > len(logs) {
			fmt.Printf("Too many block spedups. Got=%d, expected=%d\n", len(blockSpeedups), len(logs))
			return 1
		}

	}

	outdir := fmt.Sprintf("%s/concurrent-batched-%d-%s", destdir, totalTracesUsed, FormatAccessFlags(accessFlags))
	if !debug {
		if err := os.MkdirAll(outdir, 0755); err != nil {
			log.Error("Couldn't create output directory for this run", "dir", outdir, "err", err)
			return 1
		}

		// if we're debugging we just care about the computation, 
		// kDiameterHistograms and kSpeedupHistograms are now final and we can plot the graphs
		for k, floatHistogram := range kSpeedupHistograms {
			var speedupfn string
			if k == -1 {
				// this is the infinite run
				speedupfn = fmt.Sprintf("%s/infinite-cores-speedup-histogram.csv", outdir)
			} else {
				speedupfn = fmt.Sprintf("%s/finite-%d-cores-speedup-histogram.csv", outdir, k)
			}

			err := writeFloatHistogramToFile(floatHistogram, speedupfn, 0.25)
			if err != nil {
				log.Error("Error writing float histogram to file.", "err", err)
				return 1
			} else {
				log.Info("Successfully wrote float histogram data.", "file", speedupfn)
			}

			var keys []float64
			for key := range floatHistogram {
				keys = append(keys, key)
			}
			sort.Float64s(keys)
			fmt.Printf("Histogram with a bin width of %g:\n", 0.25)
			for _, key := range keys {
				fmt.Printf("[%g - %g] %d elements\n", key, key+0.25, floatHistogram[key])
			}
		}
	}

	speedupsFn := fmt.Sprintf("%s/block-speedups.csv", outdir)
	log.Info("Writing speedups to file", "file", speedupsFn, "num speedups", len(blockSpeedups))
	if err := writeSpeedupsToFile(blockSpeedups, speedupsFn); err != nil {
		fmt.Printf("Error wriging blocl speedups to file: %v", err)
		return 1
	}

	return 0
}

// we want the relevant 
func SimMultipleFiniteCoresBatched(blockTraces []*BlockTrace, krange []int, debug bool, filterFlags AccessType, listConflicts bool) (map[int]FloatHistogram, []*BlockSpeedup) {
	blockGraphs := make([]*WeightedVertexGraph, 0, len(blockTraces))

	// finite cores for each number of cores K in krange
	//kDiameterMap := make(map[int]IntHistogram)
	kSpeedupMap := make(map[int]FloatHistogram)
	blockSpeedups := make([]*BlockSpeedup, 0, len(blockTraces))

	//gasSpeedups := make([]float64, 0, len(blockTraces))
	gasSpeedups := []float64{}
	log.Info(fmt.Sprintf("Processing %d batches for ininite cores.", len(blockTraces)))
	for _, trace := range blockTraces {
		g := BlockGraph(trace, filterFlags, listConflicts)
		blockGraphs = append(blockGraphs, g)
		//concurrent := g.Diameter() + 1
		//sequential := g.NumVertices()
		//percent := float64(sequential)/float64(concurrent)
		//speedups = append(speedups, percent)
		//diameters = append(diameters, concurrent)
		
		concurrent := g.HeaviestPath()
		sequential := g.TotalVertexWeight()
		var speedup float64
		if sequential == 0 {
			speedup = float64(0)
		} else {
			speedup = float64(sequential)/float64(concurrent)
		}
		gasSpeedups = append(gasSpeedups, speedup)
		blockSpeedup := &BlockSpeedup{
			BlockNumber:	trace.BlockNumber,
			Sequential:		sequential,
			Equivalent:		map[int]uint64{
								-1: concurrent,
							},
		}
		blockSpeedups = append(blockSpeedups, blockSpeedup)
	}	


	log.Info("Saving infinite cores data.")
	//infiniteDiametersHist := createHistogram(diameters, 1)
	infiniteSpeedupHist := createFloatHistogram(gasSpeedups, 0.25)
	//kDiameterMap[-1] = infiniteDiametersHist
	kSpeedupMap[-1] = infiniteSpeedupHist
	//HistogramWriteFile(diameters, 1, fmt.Sprintf("%s/infinite-cores-histogram.csv", outdir))
	//FloatHistogramWriteFile(speedups, 0.25, fmt.Sprintf("%s/infinite-cores-speedup-historam.csv", outdir))

	for _, K := range krange {
		//diameters := []int{}
		//speedups := []float64{}
		//totalGas := []int{}
		//gasSpeedups := make([]float64, 0, len(blockTraces))
		gasSpeedups := []float64{}
		log.Info(fmt.Sprintf("Processing %d batches for %d cores.", len(blockTraces), K))
		for i, bgraph := range blockGraphs {
			g := bgraph.Copy()
			g.FiniteCores(K)
			//concurrent := g.Diameter() + 1
			//sequential := g.NumVertices()
			//percent := float64(sequential)/float64(concurrent)
			//speedups = append(speedups, percent)
			//diameters = append(diameters, concurrent)
			concurrent := g.HeaviestPath()
			sequential := g.TotalVertexWeight()
			var speedup float64
			if sequential == 0 {
				speedup = float64(0)
			} else {
				speedup = float64(sequential)/float64(concurrent)	
			}
			//sequentialGas := int(g.TotalVertexWeight())
			//concurrentGas := int(g.MaxWeightedVertexPath())
			//percent = float64(sequentialGas)/float64(concurrentGas)
			//totalGas = append(totalGas, sequentialGas)
			gasSpeedups = append(gasSpeedups, speedup)
			blockSpeedups[i].Equivalent[K] = concurrent
			if debug {
				log.Info("Speedup", "K", K, "sequential", sequential, "concurrentGas", concurrent, "speedup", speedup)
			}
		}
		

		log.Info("Saving finite cores data.")
		//diameterHist := createHistogram(diameters, 1)
		speedupHist := createFloatHistogram(gasSpeedups, 0.25)
		//kDiameterMap[K] = diameterHist
		kSpeedupMap[K] = speedupHist
		//HistogramWriteFile(diameters, 1, fmt.Sprintf("%s/finite-%d-cores-histogram.csv", outdir, K))
		//FloatHistogramWriteFile(speedups, 0.25, fmt.Sprintf("%s/finite-%d-cores-speedup-histogram.csv", outdir, K))
	}

	return kSpeedupMap, blockSpeedups
}


var FilterAddrs = map[common.Address]bool{
	//common.HexToAddress("0xA4b05FffffFffFFFFfFFfffFfffFFfffFfFfFFFf"):true,
}

func BlockGraph(blockTrace *BlockTrace, filterFlags AccessType, listConflicts bool) *WeightedVertexGraph {
	// have: reads and writes per transaction
	// want: transactions per read and write
	txWrites := make(map[KeyPair]map[int]bool)
	txReads := make(map[KeyPair]map[int]bool)
	conflicts := make(map[Conflict]bool)

	txidx := 0
	weights := make([]uint64, 0, len(blockTrace.Traces))
	for i := 0; i < len(blockTrace.Traces); i++ {
		txTrace := blockTrace.Traces[i]
	
		// filter the tx trace by the input filter
		//writeAccesses, readAccesses := FilterAccesses(txTrace, filterFlags)
		writeAccesses, readAccesses := FilterAccessesAndByAddress(txTrace, filterFlags, FilterAddrs)

		// process the reads in this transactions and determine conflits
		for _, access := range readAccesses {
			pair := access.Pair	
			_, exists := txReads[pair]
			if !exists {
				txReads[pair] = make(map[int]bool)
			}
			txReads[pair][txidx] = true

			// if previous transactions wrote this pair and this transaction reads it
			// then this is a conflict to mark
			writeTxs, exists := txWrites[pair]
			if exists {
				for wtx := range writeTxs {
					if txidx != wtx {
						conflicts[Conflict{txidx, wtx}] = true
					}
				}
			}
		}

		// process the writes and add write-write conflicts if they exist
		for _, access := range writeAccesses {
			pair := access.Pair
			writeTxs, exists := txWrites[pair]
			if exists {
				for wtx := range writeTxs {
					if txidx != wtx {
						conflicts[Conflict{txidx, wtx}] = true
					}
				}
			} else {
				txWrites[pair] = make(map[int]bool)
			}
			txWrites[pair][txidx] = true
		}
		weights = append(weights, txTrace.GasUsed)
		txidx++
	}

	// if --list-conflicts print out the conflicts that exist across all transactions in this block
	if listConflicts {
		// reads by all: the keys in txReads s.t. len(txReads[k]) == txidx
		readByAll := make(map[KeyPair]bool)
		for pair, txs := range txReads {
			if len(txs) == txidx-1 {
				readByAll[pair] = true	
			}
		}
		// same for writes
		writtenByAll := make(map[KeyPair]bool)
		for pair, txs := range txWrites {
			if len(txs) == txidx-1 {
				writtenByAll[pair] = true
			}
		}

		// print them out
		log.Debug("Keys that conflict across all tranasctions.")
		fmt.Printf("Reads: \n\t")
		for pair := range readByAll {
			fmt.Printf("%v, ", pair)
		}
		fmt.Println()
	
		fmt.Printf("Writes: \n\t")
		for pair := range writtenByAll {
			fmt.Printf("%v, ", pair)
		}
		fmt.Println()
	}

	if len(weights) > 0 {
		graph := NewWeightedVertexGraph(weights, int(blockTrace.BlockNumber.Int64()))
		if len(conflicts) > 0 {
			for cn := range conflicts {
				err := graph.AddEdge(cn.tx1, cn.tx2)
				if err != nil {
					log.Error("Failed to add a conflict edge.", "err", err, "tx1", cn.tx1, "tx2", cn.tx2)
					graph.Display("Conflicts")
					panic("")
				}
			}
		}
		//log.Info("Block", "number", blockTrace.BlockNumber, "txidx", txidx, "conflicts", len(conflicts), "graph", graph.Diameter())
		return &graph
	}
	log.Info("Empty graph")
	return nil
}
