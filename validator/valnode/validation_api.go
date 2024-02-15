// Copyright 2023-2024, Offchain Labs, Inc.
// For license information, see https://github.com/OffchainLabs/nitro/blob/master/LICENSE

package valnode

import (
	"context"
	"encoding/base64"
	"errors"
	"fmt"
	"log"
	"math/rand"
	"os"
	"strings"
	"strconv"
	"sync"
	"time"
	_ "reflect"
	"encoding/gob"
	"sort"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/ethereum/go-ethereum/trie"

	"github.com/offchainlabs/nitro/util/stopwaiter"
	"github.com/offchainlabs/nitro/validator"
	"github.com/offchainlabs/nitro/validator/server_api"
	"github.com/offchainlabs/nitro/validator/server_arb"
)

const Namespace string = "validation"
const subTrieDepth = 0

var logFile *os.File
var firstValidationInput bool
var pathToSubTrieRoot []int
var cacheSubTrie *trie.ValidatorTrie
var numSuccessfulValidations int
var validationLock *sync.Mutex
var lastInputNumber uint64
var bufferedValidations map[uint64](*validator.ValidationInput)
var allIdsSeen map[uint64]bool
var rootHashes map[uint64](common.Hash)
// var lastRoot *root

type ValidationServerAPI struct {
	spawner validator.ValidationSpawner
}

func (a *ValidationServerAPI) Name() string {
	log.Println("\n*** Getting the god damn validation name")
	return a.spawner.Name()
}

func (a *ValidationServerAPI) Room() int {
	return a.spawner.Room()
}

// need the root node
// all shortNodes are paired with either a Leaf or a Fullnode (an extension node)
// id shortNodes by prefix:
//			if child is branch node: the prefix doesn't chage, only node is deleted
//			if child is a leaf: the prefix doesn't change, only node value changes
// changed branch node:
// 			if the value of a child node in a known index of a branch node is
//
// store nodes in a map with

func blockHeaderFromInput(valInput *validator.ValidationInput) (*types.Header) {
	// get block header
	blockHash := valInput.StartState.BlockHash
	rawBlockHeader := valInput.Preimages[blockHash]
	firstBlockHeader := &types.Header{}
	err := rlp.DecodeBytes(rawBlockHeader, &firstBlockHeader)
	if err != nil { panic(fmt.Errorf("Couldn't decode block header.")) }
	firstBlockHeader.SanityCheck()
	return firstBlockHeader
}

func InitializeCache(valInput *validator.ValidationInput) (bool) {
	firstBlockHeader := blockHeaderFromInput(valInput)

	// get root node
	rootNodeRaw := valInput.Preimages[firstBlockHeader.Root]
	rootNode, _ := trie.PublicDecodeNode(firstBlockHeader.Root.Bytes(), rootNodeRaw)
	log.Println("[Init] Root Hash:", firstBlockHeader.Root)
	
	f, err := os.Create("/home/sbakshi/caching/initcacheoutput.txt")
	if err != nil { panic(err) }

	// grab a random path to fullNode
	randomPath, b := trie.ChooseRandomFullNode(rootNode, valInput.Preimages, subTrieDepth)
	if !b { panic("failed to find any fullnode") }
	pathToSubTrieRoot = randomPath
	log.Println("[Init] Index path of chosen full node:", randomPath)

	f.WriteString(fmt.Sprintf("Index path of chosen node: %v\n", randomPath))

	// get node from path
	n, exists := trie.NodeFromPath(rootNode, randomPath, valInput.Preimages)
	if !exists { panic("chosen full node in init should always exist") }
	log.Println("[init] cache subtrie root:", n)

	f.WriteString(fmt.Sprintf("subtrie root: %v\n", n))

	// build trie from n
	subTrieHashes := trie.TrieFromNode(n, valInput.Preimages)
	// must also include hash of fullNode root!
	rootHash := trie.HashNode(n)
	log.Println(fmt.Sprintf("[Init] Saving preimage of fullNode root: %v", rootHash))

	// save only these into a validator trie
	subTriePreimages := make(map[common.Hash][]byte)
	subTriePreimages[rootHash] = valInput.Preimages[rootHash]
	log.Println(fmt.Sprintf("[Init] Number of preimages in the subtrie: %v", len(subTrieHashes) + 1))
	for _, pi := range subTrieHashes {
		_, exists := valInput.Preimages[pi]
		if !exists { panic(fmt.Sprintf("TrieFromNode selected a pre-image that isn't in valnput: %v", pi)) }
		subTriePreimages[pi] = valInput.Preimages[pi]
	}

	cacheSubTrie = &trie.ValidatorTrie{
					Root: n,
					Nodes: subTriePreimages,
					Pathmap: make(map[string]common.Hash),
					Mutex: &sync.RWMutex{},
	}
	//ok := cacheSubTrie.InitPathmap()

	//if !ok { 
	//	log.Println("[Init] Failed to init the path map")
	//	f.WriteString("Failed to init the path map\n")
	//} else { f.WriteString("Path map successful\n") }
	ok := true

	f.Close()

	firstValidationInput = false
	return (ok && true)
}

func processValidationInput(valInput *validator.ValidationInput) bool {
	if valInput.Id != lastInputNumber + 1 {
		panic(fmt.Sprintf("Processing out of order. Oldid=%v, newId=%v", lastInputNumber, valInput.Id))
	}
	// process new validation request see if there is a change in the root or the cache trie root
	prevRoot := cacheSubTrie.Root
	trie.HashNode(prevRoot)

	// get root for this request
	blockHeader := blockHeaderFromInput(valInput)
	rootNodeRaw := valInput.Preimages[blockHeader.Root]
	rootNode, _ := trie.PublicDecodeNode(blockHeader.Root.Bytes(), rootNodeRaw)

	// see if the cache subtrie root exists in this request
	newRoot, ok := trie.NodeFromPath(rootNode, pathToSubTrieRoot, valInput.Preimages)
	if ok {
		// if the root has hasn't changed then sanity check
		newRootHash := trie.HashNode(newRoot)
		oldRootHash := trie.HashNode(cacheSubTrie.Root)
		if (newRootHash == oldRootHash) {
			//cacheSubTrie.SanityCheck(newRoot, valInput.Preimages)
			// do nothing for now
			b := trie.SameChildren(newRoot, cacheSubTrie.Root)
			if !b {
				panic("full nodes with the same hash have different children")
			}
			return true
		} else {
			// something must have changed
			success := cacheSubTrie.TrieUpdate(newRoot, valInput.Preimages)
			if !success {
				log.Println("Couldn't update the cache trie")
				return false
			} else {
				log.Println("Successfully updated the cache trie")
				// reset the trie root
				cacheSubTrie.Root = newRoot
				log.Println(fmt.Sprintf("New Root. Hash=%v, Node=%v", trie.HashNode(newRoot), newRoot))
				numNodes := cacheSubTrie.NumNodesWithStorage()
				log.Println("Nodes in trie AFTER update:", numNodes)
				size := cacheSubTrie.SizeInBytesWithStorage()
				log.Println("Size of trie AFTER update:", size)
				return true
			}
		}
	} else {
		return true
	}
}

// variables used to for saving validation inputs received 
var  inputsToSave [](*validator.ValidationInput)				// the list of validation inputs saved to one file
var fnBase = "/home/sbakshi/caching/validator_logs/valinput"	// base dir of saved inputs
var firstId uint64												// the first validation input processed

// determine the file name for a particular set of inputs by Id
func fileNameRange(start uint64, end uint64) string {			
	return fmt.Sprintf("%s-%d-%d.log", fnBase, start, end)
}

// ensure SAVED log files are in order
func SortFileNameAscend(files []os.FileInfo) {
	sort.Slice(files, func(i, j int) bool {
		return files[i].Name() < files[j].Name()
	})
}

// This function reads SAVED validation inputs and processes them normally
// As opposed to func validate(..) which is called when an input is received from a client
func processSavedInputs() bool {
	dir := "/home/sbakshi/caching/validator_logs"
	d, err := os.Open(dir)
	if err != nil {
		panic(err)
	}

	files, err := d.Readdir(0)
	if err != nil {
		panic(err)
	}

	SortFileNameAscend(files)	

	var vinput (validator.ValidationInput)
	for _, v := range files {
		log.Println(v.Name())
		// open file
		fn := fmt.Sprintf("%s/%s", dir, v.Name())
		f, err := os.Open(fn)
		if err != nil {
			panic(err)
		}


		startId, err := strconv.Atoi(strings.Split(strings.Split(v.Name(), ".")[0], "-")[1])
		if err != nil {
			panic(err)
		}
		endId, err := strconv.Atoi(strings.Split(strings.Split(v.Name(), ".")[0], "-")[2])
		if err != nil {
			panic(err)
		}
		log.Println(fmt.Sprintf("start=%d, end=%d", startId, endId))

		dec := gob.NewDecoder(f)
		for i := startId; i <= endId; i++ {
			// get valInput from the file
			err = dec.Decode(&vinput)
			if err != nil {
				panic(err)
			}
			processInput(&vinput)
		}
		f.Close()
	}
	d.Close()

	return true
}

// DEBUG function to search for specific preimages in the saved data
func findPreimageInFiles() {
	//preimage := common.HexToHash("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")
	preimage := common.HexToHash("3b44b8c856a5f7ad22d92bb8a05b9a1d3cde48edaebdd4b73d229ad01709f7cc")
	dir := "/home/sbakshi/caching/validator_logs"
	d, err := os.Open(dir)
	if err != nil {
		panic(err)
	}

	files, err := d.Readdir(0)
	if err != nil {
		panic(err)
	}
	var vinput (validator.ValidationInput)
	for _, v := range files {
		log.Println(v.Name())
		// open file
		fn := fmt.Sprintf("%s/%s", dir, v.Name())
		f, err := os.Open(fn)
		if err != nil {
			panic(err)
		}
		startId, err := strconv.Atoi(strings.Split(strings.Split(v.Name(), ".")[0], "-")[1])
		if err != nil {
			panic(err)
		}
		endId, err := strconv.Atoi(strings.Split(strings.Split(v.Name(), ".")[0], "-")[2])
		if err != nil {
			panic(err)
		}
		dec := gob.NewDecoder(f)
		for i := startId; i <= endId; i++ {
			// get valInput from the file
			err = dec.Decode(&vinput)
			if err != nil {
				panic(err)
			}
			_, exists := vinput.Preimages[preimage]
			if exists {
				log.Println(fmt.Sprintf("The preimage exists in input %d in file %s", vinput.Id, v.Name()))
			}
		}
		f.Close()
	}
	
}


// function is used to process both live validation inputs (called by function `Validate(..)`)
// and by offline validation of saved inputs (called by `processSavedInputs`)
// on first activation defines the cache subtrie root randomly, initialized all variables
// on later activations it updaes the cache sub trie with the new input.
// CURRENTLY: it does no eviction but only tries to add new paths in the trie as they appear in inputs
//		      and update the existing trie as the hashes change
func processInput(valInput *validator.ValidationInput) (bool) {
	validationLock.Lock()
	blockHeader :=blockHeaderFromInput(valInput)
	if firstValidationInput {
		log.Println("First batch Number:", valInput.StartState.Batch)
		
		// initalizes cache variables in the trie module
		initSuccess := InitializeCache(valInput)
		if !initSuccess { panic("always true") }	

		// print the root and determine the cache trie's # nodes
		subTrieRootHash := trie.HashNode(cacheSubTrie.Root)
		log.Println(fmt.Sprintf("[Sanity] cacheroot hash: %v", subTrieRootHash))
		numNodes := cacheSubTrie.NumNodesWithStorage()
		log.Println("[Sanity] Nodes in cache:", numNodes)

		// DEBUG: writing things to a log file (NOT NEEDED ANYMORE)
		f, err := os.Open("/home/sbakshi/caching/initcacheoutput.txt")
		if err != nil { panic(fmt.Sprintf("%v",err)) }

		// size of trie in bytes
		trieSize := cacheSubTrie.SizeInBytesWithStorage()
		log.Println("[Sanity] Trie size in bytes:", trieSize)

		// get root for this request input an do some sanity checks on our processing
		rootNodeRaw := valInput.Preimages[blockHeader.Root]
		rootNode, _ := trie.PublicDecodeNode(blockHeader.Root.Bytes(), rootNodeRaw)

		// just checks that our cache is created correctly, our hashing is done correctly
		// check that if we run `NodeHashFromPath` with the path chosen above that we arrive at the same hash
		rootHashFromPath, exists := trie.NodeHashFromPath(rootNode, pathToSubTrieRoot, valInput.Preimages)
		f.WriteString(fmt.Sprintf("Nodes in trie: %d\nsize of trie: %d\n", numNodes, trieSize))
		if !exists {
			log.Println("[Sanity] Couldn't retrieve root from preimages right after init cache")
			f.WriteString(fmt.Sprintf("Couldn't retreive root from preimages right after init cache\n"))
			time.Sleep(30 * time.Second)
		} else {
			log.Println("[Sanity] Everything okay after init cache so something is getting garbage collected")
			log.Println("[Sanity] root hash fro path", rootHashFromPath)
			// look it up again
			_, exists := cacheSubTrie.Nodes[rootHashFromPath]
			log.Println(fmt.Sprintf("Root hash (%v) exists in Nodes?: %v", rootHashFromPath, exists))
			f.WriteString(fmt.Sprintf("Everything okay after init cache"))
		}
		f.Close()

		// set up some state variables
		lastInputNumber = valInput.Id
		allIdsSeen[valInput.Id] = true
		rootHashes[valInput.Id] = blockHeader.Root
	} else {
		// process new validation request see if there is a change in the root or the cache trie root
		_, exists := allIdsSeen[valInput.Id]
		if exists {
			// sanity: if repeat then ensure that the same input ID corresponds to the same block header
			// if so ignore it because it's a duplicate input
			blockHeader := blockHeaderFromInput(valInput)
			previousRootHash, exists := rootHashes[valInput.Id]
			if !exists {
				panic("root hash for EXISTING valInput doesn't exist")
			} else if previousRootHash != blockHeader.Root {
				panic("same id for validation request but different roots")
			} // else it exists and they are the same 
		} else {
			// mark this Id as seen
			allIdsSeen[valInput.Id] = true
			rootHashes[valInput.Id] = blockHeader.Root

			// if our of order buffer it for later
			if valInput.Id != lastInputNumber + 1 {
				// save it in the map for later
				bufferedValidations[valInput.Id] = valInput
			} else {
				// process this one because it's next
			    ok := processValidationInput(valInput)
				if !ok {
					log.Println(fmt.Sprintf("Couldn't propoerly update the cache"))
				}
				lastInputNumber = valInput.Id
				// loop through all successors that may be buffered and delete them from the map 
				for {
					r := lastInputNumber + 1
					inp, exists := bufferedValidations[r]
					if exists {
						// process it
						ok = processValidationInput(inp)
						if !ok {
							log.Println(fmt.Sprintf("Couldn't propoerly update the cache"))
						}
						lastInputNumber = inp.Id
						delete(bufferedValidations, inp.Id)
					} else {
						// there are no more left to process wait for another call
						break
					}
				}
			}
		}
	}

	// DEBUG: just print informations to show that something is happening in the terminal
	numSuccessfulValidations += 1
	if (numSuccessfulValidations % 100 == 1) {
		log.Println(fmt.Sprintf("Validated %v requests.", numSuccessfulValidations))
	}
	validationLock.Unlock()

	return true
}

var numSaved int

// add another validation input to be saved to file
// once we've buffered 100 in `inputsToSave`, write them all to a file
func saveToFile(valInput *validator.ValidationInput) bool {
	if (len(inputsToSave) == 100) {
		// get the first and last Ids	
		startId := inputsToSave[0].Id
		endId := inputsToSave[99].Id
		fn := fileNameRange(startId, endId)
		f, err := os.Create(fn)
		if err != nil { panic(err) }
		log.Println(fmt.Sprintf("Saving inputs %d to %d", startId, endId))

		encoder := gob.NewEncoder(f)
		for _,inp := range(inputsToSave) {
			err = encoder.Encode(inp)
			if err != nil {
				panic(err)
			}
		}
		// close the file
		f.Close()
		// clear the variables
		inputsToSave = [](*validator.ValidationInput){}
	}
	// append the valInput to the list
	inputsToSave = append(inputsToSave, valInput)
	return true
}

// run `Validate(..)` with this to just save inputs
func runCollectionMode(valInput *validator.ValidationInput) bool {
	if firstValidationInput {
		numSaved = 1
		lastInputNumber = valInput.Id
		firstValidationInput = false
		inputsToSave = [](*validator.ValidationInput){valInput}
		firstId = valInput.Id
	} else {
		// save 5000 in-order inputs
		if numSaved <= 5000 {
			if valInput.Id > lastInputNumber + 1 {
				bufferedValidations[valInput.Id] = valInput
			} else if valInput.Id == (lastInputNumber + 1) {
				ok := saveToFile(valInput)
				numSaved = numSaved + 1
				lastInputNumber = valInput.Id
				// loop through all successors until they don't exist
				for {
					r := lastInputNumber + 1
					inp, exists := bufferedValidations[r]
					if exists {
						//log.Println(fmt.Sprintf("There are waitin inputs r=%v",r))
						// process it
						ok = saveToFile(inp)
						if !ok {
							log.Println(fmt.Sprintf("Couldn't propoerly update the cache"))
						}
						lastInputNumber = inp.Id
						numSaved = numSaved + 1
						delete(bufferedValidations, inp.Id)
					} else {
						// there are no more left to process wait for another call
						break
					}
				}
			}
		} else if numSaved == 1500+1 {
			log.Println("Done collecting data")
		}
	}
	return true
}

var collection bool
// Modified validate does no validation but on first call, selects a random fullnode in the trie as it's cache root
// saves all the necessary information, and uses the trie module to create the subtrie
// it only processes validation inputs in order and buffers future ones for when it's time
// if the cache subtrie root exists in a validationInput, it tries to update the trie: traverse both tries in parallel, add new subtries as they appear
//																				       update nodes that have updated (maybe a child hash changed in a fullNode)
func (a *ValidationServerAPI) Validate(ctx context.Context, entry *server_api.InputJSON, moduleRoot common.Hash) (validator.GoGlobalState, error) {
	validationLock.Lock()
	valInput, err := server_api.ValidationInputFromJson(entry)
	if err != nil {
		return validator.GoGlobalState{}, err
	}

	if collection == true {
		runCollectionMode(valInput)
	} else {
		processInput(valInput)
	}

	numSuccessfulValidations += 1
	if (numSuccessfulValidations % 100 == 1) {
		log.Println(fmt.Sprintf("Validated %v requests.", numSuccessfulValidations))
	}
	validationLock.Unlock()
	return validator.GoGlobalState{}, err
}

func (a *ValidationServerAPI) WasmModuleRoots() ([]common.Hash, error) {
	return a.spawner.WasmModuleRoots()
}

func NewValidationServerAPI(spawner validator.ValidationSpawner) *ValidationServerAPI {
	log.Println("Starting log file")
	validationLock = &sync.Mutex{}
	firstValidationInput = true
	numSuccessfulValidations = 0
	bufferedValidations = make(map[uint64](*validator.ValidationInput))
	allIdsSeen = make(map[uint64]bool)
	rootHashes = make(map[uint64](common.Hash))

	// false = run it live and process from client
	// true = just collect and save inputs to file
	collection = false

	// DEBUG: run this command to process the saved validation inputs
	// else comment both out and run validator live
	processSavedInputs()
	//findPreimageInFiles()

	return &ValidationServerAPI{spawner}
}

type execRunEntry struct {
	run      validator.ExecutionRun
	accessed time.Time
}

type ExecServerAPI struct {
	stopwaiter.StopWaiter
	ValidationServerAPI
	execSpawner validator.ExecutionSpawner

	config server_arb.ArbitratorSpawnerConfigFecher

	runIdLock sync.Mutex
	nextId    uint64
	runs      map[uint64]*execRunEntry
}

func NewExecutionServerAPI(valSpawner validator.ValidationSpawner, execution validator.ExecutionSpawner, config server_arb.ArbitratorSpawnerConfigFecher) *ExecServerAPI {
	log.Println("\n*** new execution server api")
	return &ExecServerAPI{
		ValidationServerAPI: *NewValidationServerAPI(valSpawner),
		execSpawner:         execution,
		nextId:              rand.Uint64(), // good-enough to aver reusing ids after reboot
		runs:                make(map[uint64]*execRunEntry),
		config:              config,
	}
}

func (a *ExecServerAPI) CreateExecutionRun(ctx context.Context, wasmModuleRoot common.Hash, jsonInput *server_api.InputJSON) (uint64, error) {
	log.Println("\n*** CreateExecutionRun")
	input, err := server_api.ValidationInputFromJson(jsonInput)
	if err != nil {
		return 0, err
	}
	execRun, err := a.execSpawner.CreateExecutionRun(wasmModuleRoot, input).Await(ctx)
	if err != nil {
		return 0, err
	}
	a.runIdLock.Lock()
	defer a.runIdLock.Unlock()
	newId := a.nextId
	a.nextId++
	a.runs[newId] = &execRunEntry{execRun, time.Now()}
	return newId, nil
}

func (a *ExecServerAPI) LatestWasmModuleRoot(ctx context.Context) (common.Hash, error) {
	return a.execSpawner.LatestWasmModuleRoot().Await(ctx)
}

func (a *ExecServerAPI) removeOldRuns(ctx context.Context) time.Duration {
	oldestKept := time.Now().Add(-1 * a.config().ExecutionRunTimeout)
	a.runIdLock.Lock()
	defer a.runIdLock.Unlock()
	for id, entry := range a.runs {
		if entry.accessed.Before(oldestKept) {
			delete(a.runs, id)
		}
	}
	return a.config().ExecutionRunTimeout / 5
}

func (a *ExecServerAPI) Start(ctx_in context.Context) {
	a.StopWaiter.Start(ctx_in, a)
	a.CallIteratively(a.removeOldRuns)
}

func (a *ExecServerAPI) WriteToFile(ctx context.Context, jsonInput *server_api.InputJSON, expOut validator.GoGlobalState, moduleRoot common.Hash) error {
	input, err := server_api.ValidationInputFromJson(jsonInput)
	if err != nil {
		return err
	}
	_, err = a.execSpawner.WriteToFile(input, expOut, moduleRoot).Await(ctx)
	return err
}

var errRunNotFound error = errors.New("run not found")

func (a *ExecServerAPI) getRun(id uint64) (validator.ExecutionRun, error) {
	a.runIdLock.Lock()
	defer a.runIdLock.Unlock()
	entry := a.runs[id]
	if entry == nil {
		return nil, errRunNotFound
	}
	entry.accessed = time.Now()
	return entry.run, nil
}

func (a *ExecServerAPI) GetStepAt(ctx context.Context, execid uint64, position uint64) (*server_api.MachineStepResultJson, error) {
	run, err := a.getRun(execid)
	if err != nil {
		return nil, err
	}
	step := run.GetStepAt(position)
	res, err := step.Await(ctx)
	if err != nil {
		return nil, err
	}
	return server_api.MachineStepResultToJson(res), nil
}

func (a *ExecServerAPI) GetProofAt(ctx context.Context, execid uint64, position uint64) (string, error) {
	run, err := a.getRun(execid)
	if err != nil {
		return "", err
	}
	promise := run.GetProofAt(position)
	res, err := promise.Await(ctx)
	if err != nil {
		return "", err
	}
	return base64.StdEncoding.EncodeToString(res), nil
}

func (a *ExecServerAPI) PrepareRange(ctx context.Context, execid uint64, start, end uint64) error {
	run, err := a.getRun(execid)
	if err != nil {
		return err
	}
	_, err = run.PrepareRange(start, end).Await(ctx)
	return err
}

func (a *ExecServerAPI) ExecKeepAlive(ctx context.Context, execid uint64) error {
	_, err := a.getRun(execid)
	if err != nil {
		return err
	}
	return nil
}

func (a *ExecServerAPI) CloseExec(execid uint64) {
	a.runIdLock.Lock()
	defer a.runIdLock.Unlock()
	run, found := a.runs[execid]
	if !found {
		return
	}
	run.run.Close()
	delete(a.runs, execid)
}
