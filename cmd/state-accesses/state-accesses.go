package main

import (
	"os"
	"fmt"
	"math"
	"strconv"

	"github.com/ethereum/go-ethereum/log"
	_"github.com/ethereum/go-ethereum/common"
	_"github.com/ethereum/go-ethereum/core/types"
)

func main() {
	os.Exit(mainImpl())
}

func mainImpl() int {
	log.SetDefault(log.NewLogger(log.NewTerminalHandlerWithLevel(os.Stderr, log.LevelDebug, true)))
	
	if len(os.Args[1:]) < 3 {
		log.Error("Not enough arguments", "args", os.Args, "expected", "./target/bin/state-accesses <datadir> <destdir> <limit>")
		return 1
	}

	datadir := os.Args[1]
	destdir := os.Args[2]
	limit, err := strconv.Atoi(os.Args[3])
	if err != nil {
		log.Error("Couldn't parse input limit", "limit", os.Args[3], "err", err)
		return 1
	}

	log.Info("Input params", "datadir", datadir, "destdir", destdir, "limit", limit)

	if limit == -1 {
		limit = math.MaxInt
	}

	sortedFiles, err := getSortedTraceFiles(datadir)
	if err != nil {
		log.Error("Faled", "err", err)
		return 1
	}

	log.Info("Block access data", "first", sortedFiles[0].num, "last", sortedFiles[len(sortedFiles)-1].num)

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
		actuallyUsed++
	}

	krange := []int{2, 4, 8, 16}
	accessFlags := AccessOpcode | AccessCode
	// the output directory of all these files is determined by the access flags and limit
	outdir := fmt.Sprintf("%s/concurrent-%d-%s", destdir, actuallyUsed, FormatAccessFlags(accessFlags))

	if err := os.MkdirAll(outdir, 0755); err != nil {
		log.Error("Couldn't create output directory for this run", "dir", outdir)
		return 1
	}	
	
	log.Info("Outdir", "outdir", outdir)

	SimMultipleFiniteCores(blockTraces, actuallyUsed, krange, outdir, accessFlags)

	return 0
}

func SimMultipleFiniteCores(blockTraces []*BlockTrace, limit int, krange []int, outdir string, filterFlags AccessType) {
	blockGraphs := make([]*WeightedVertexGraph, 0, len(blockTraces))
	diameters := []int{}
	speedups := []float64{}

	totalGas := []int{}
	gasSpeedups := []float64{}
	for _, trace := range blockTraces {
		g := BlockGraph(trace, filterFlags)
		blockGraphs = append(blockGraphs, g)
		concurrent := g.Diameter() + 1
		sequential := g.NumVertices()
		percent := float64(sequential)/float64(concurrent)
		speedups = append(speedups, percent)
		diameters = append(diameters, concurrent)
		
		sequentialGas := int(g.TotalVertexWeight())
		concurrentGas := int(g.MaxWeightedVertexPath())
		percent = float64(sequentialGas)/float64(concurrentGas)
		totalGas = append(totalGas, sequentialGas)
		gasSpeedups = append(gasSpeedups, percent)
	}	


	HistogramWriteFile(diameters, 1, fmt.Sprintf("%s/infinite-cores-histogram.csv", outdir))
	FloatHistogramWriteFile(speedups, 0.25, fmt.Sprintf("%s/infinite-cores-speedup-historam.csv", outdir))


	// finite cores for each number of cores K in krange
	for _, K := range krange {
		diameters := []int{}
		speedups := []float64{}

		totalGas := []int{}
		gasSpeedups := []float64{}
		for _, bgraph := range blockGraphs {
			g := bgraph.Copy()
			g.FiniteCores(K)
			concurrent := g.Diameter() + 1
			sequential := g.NumVertices()
			percent := float64(sequential)/float64(concurrent)
			speedups = append(speedups, percent)
			diameters = append(diameters, concurrent)
			
			sequentialGas := int(g.TotalVertexWeight())
			concurrentGas := int(g.MaxWeightedVertexPath())
			percent = float64(sequentialGas)/float64(concurrentGas)
			totalGas = append(totalGas, sequentialGas)
			gasSpeedups = append(gasSpeedups, percent)
		}
		HistogramWriteFile(diameters, 1, fmt.Sprintf("%s/finite-%d-cores-histogram.csv", outdir, K))
		FloatHistogramWriteFile(speedups, 0.25, fmt.Sprintf("%s/finite-%d-cores-speedup-histogram.csv", outdir, K))
	}
}


func BlockGraph(blockTrace *BlockTrace, filterFlags AccessType) *WeightedVertexGraph {
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
		writeAccesses, readAccesses := FilterAccesses(txTrace, filterFlags)

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
		//log.Info("Block", "number", blockTrace.BlockNumber, "txidx", txidx, "conflicts", len(conflicts), "graph", graph.Diameter(), "sequential", graph.TotalVertexWeight(), "weighted", graph.MaxWeightedVertexPath())
		return &graph
	}
	log.Info("Empty graph")
	return nil
}
