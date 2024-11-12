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
	_"encoding/hex"
	"sort"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/ethdb"
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
const cacheSize = 50000
var logFile *os.File
var firstValidationInput bool
var pathToSubTrieRoot []int
var cacheSubTrie *trie.ValidatorTrie
var cacheSubTriePrefix []byte
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

type TestCache struct {
	trie *trie.ValidatorTrie
	prefix []byte
	contents []common.Hash
	//fifo []uint8
	hashToIdx map[common.Hash]int
	//fifo map[common.Hash]uint8
	fifo []uint8
	pointer int
}

var cache *TestCache

func (c *TestCache) Update(up *trie.CacheUpdate) {
	// TODO: we don't care about the number of writes yet

	// check that the writes are a subset of accesses
	writesNotAccesses := l1NotInl2(up.NodesAdded, up.NodesAccessed)
	if len(writesNotAccesses) > 0 {
		log.Println("Accessed", up.NodesAccessed)
		log.Println("Added", up.NodesAdded)
		log.Println("DIff", writesNotAccesses)
		panic("Writes that weren't accesses")
	}

	changesNotAccessed := l1NotInl2(up.NodesChanged, up.NodesAccessed)
	if len(changesNotAccessed) > 0 {
		log.Println("Accessed", up.NodesAccessed)
		log.Println("Changed", up.NodesChanged)
		log.Println("Diff", changesNotAccessed)
		panic("Changes that weren't accessed")
	}

	writeMap := make(map[common.Hash]struct{}, len(up.NodesAdded))
	for _, x := range up.NodesAdded {
		writeMap[x] = struct{}{}
	}

	// first process the deletes, remove all of them from the cache including the shortNode parent if it is a valueNode
	for _, x := range up.NodesDeleted {
		// they aren't all accessed so let's remove them from the cache
		idxInCache, exists := c.hashToIdx[x]
		if !exists {
			panic("Delete of a key that doesn't exist in the cache")
		}

		// if this not is immediately re-added then don't count it and leave it alone
		_, alsoAdded := writeMap[x]
		if alsoAdded {
			log.Println("this node is deleted then immediately added. Most like a cast of an insertion and anode accessed agagin")
			// ignore this and remove it from the writeMap
			delete(writeMap, x)
			// ASSUME: this hash was marked as accessed by AddSubTrie so do nothing else here
			// the check above also confirms that if this is being aded than it is in accessed
			continue
		}

		// set this to 0
		c.fifo[idxInCache] = 0
		// don't need to clear contents we don't know what idxInCache will be after delete
		//c.contents[idxInCache] = common.BytesToHash(make([]byte, 32))

		// delete from hashToIdx
		delete(c.hashToIdx, x)

		// TODO: do a trie search and find+kill any dangling shortNodes that don't need to exist
	}
	
	// assert that all RecordedChanges correspond to things already in the cache
	for _, x := range up.NodesChanged {
		_, exists := c.hashToIdx[x]
		if !exists {
			panic("A change recorded on node that isn't in hashToIdx")
		}
	}

	for _, x := range up.NodesAccessed {
		_, added := writeMap[x]
		if added {
			// check that this thing doesn't already exist in the cache
			idxInCache, exists := c.hashToIdx[x]
			if exists {
				log.Println("Idx in cache", idxInCache)
				log.Println(fmt.Sprintf("%x", x))
				log.Println("fifo", c.fifo[idxInCache])
				panic("addition already in cache")
			}

			// if it's an addition move the pointer ahead until you reach a 0 slot
			i := c.pointer
			for true {
				// check if this slot is a 0
				if c.fifo[i] == 0 { 	// we can insert in this slot
					// is this slot empty or occupied?
					//var zeroHash common.Hash
					zeroHash := common.BytesToHash(make([]byte, 32))
					if zeroHash.Cmp(c.contents[i]) == 0 { 	// the slot is empty
						//log.Println("Adding to empty slot", i)
						c.hashToIdx[x] = i
						c.contents[i] = x	
						c.fifo[i] = 1
					} else {								// the slot is occupied
						// update contents and fifo
						//log.Println("Adding to occupied slot", i)
						c.hashToIdx[x] = i
						c.contents[i] = x
						c.fifo[i] = 1
					}
					// move pointer to the next one
					c.pointer = (i+1) % len(c.contents)
					break
				} else if c.fifo[i] == 1 {			// decrement and move to the next one
					c.fifo[i] = 0
					i = (i+1) % len(c.contents)
					c.pointer = i
				} else {
					panic(fmt.Sprintf("fifo can only be 0 and 1, not %v", c.fifo[i]))
				}
			}
		} else {   		// if just an access then we update the fifo values and that's it
			// assert that the item is in the cache already
			idxInCache, exists := c.hashToIdx[x]
			if !exists {
				panic("Access of item not in cache")
			}

			if c.fifo[idxInCache] == 0 {
				log.Println(fmt.Sprintf("Upgrading fifo of hash (%x, index %v) from 0 to 1", x, idxInCache))
				c.fifo[idxInCache] = 1
			} else if c.fifo[idxInCache] == 1 {
				//log.Println(fmt.Sprintf("Fifo of (%x, index %v) already 1", x, idxInCache))
			} else {
				panic(fmt.Sprintf("fifo can only be 0 and 1, not %v", c.fifo[idxInCache]))
			}
		}
	}
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
	rawBlockHeader := valInput.Preimages[0][blockHash]
	firstBlockHeader := &types.Header{}
	err := rlp.DecodeBytes(rawBlockHeader, &firstBlockHeader)
	if err != nil { panic(fmt.Errorf("Couldn't decode block header.")) }
	firstBlockHeader.SanityCheck()
	return firstBlockHeader
}


func l1NotInl2(l1 []common.Hash, l2 []common.Hash) []common.Hash {
	l2map := make(map[common.Hash]struct{}, len(l2))
	for _, x := range l2 {
		l2map[x] = struct{}{}
	}
	diff := []common.Hash{}
	for _, x := range l1 {
		if _, found := l2map[x]; !found {
			diff = append(diff, x)
		}
	}
	return diff
}


func InitializeCache(valInput *validator.ValidationInput) (bool) {
	firstBlockHeader := blockHeaderFromInput(valInput)

	// get root node
	rootNodeRaw := valInput.Preimages[0][firstBlockHeader.Root]
	rootNode, _ := trie.PublicDecodeNode(nil, rootNodeRaw)
	//rootNode, _ := trie.PublicDecodeNode(firstBlockHeader.Root.Bytes(), rootNodeRaw)
	log.Println("[Init] Root Hash:", firstBlockHeader.Root)
	log.Println(fmt.Sprintf("ROot type: %T", rootNode))
	
	f, err := os.Create("/home/sbakshi/caching/initcacheoutput.txt")
	if err != nil { panic(err) }

	// grab a random path to fullNode
	randomPath, b := trie.ChooseRandomFullNode(rootNode, valInput.Preimages[0], subTrieDepth)
	cacheSubTriePrefix = trie.PrefixFromPath(rootNode, randomPath, valInput.Preimages[0])
	if !b { panic("failed to find any fullnode") }
	pathToSubTrieRoot = randomPath
	log.Println("[Init] Index path of chosen full node:", randomPath)

	f.WriteString(fmt.Sprintf("Index path of chosen node: %v\n", randomPath))

	// get node from path
	n, exists := trie.NodeFromPath(rootNode, randomPath, valInput.Preimages[0])
	if !exists { panic("chosen full node in init should always exist") }
	log.Println("[init] cache subtrie root:", n)

	f.WriteString(fmt.Sprintf("subtrie root: %v\n", n))

	// build trie from n
	subTrieHashes := trie.TrieFromNode(n, valInput.Preimages[0])
	// must also include hash of fullNode root!
	rootHash := trie.HashNode(n)
	log.Println(fmt.Sprintf("[Init] Saving preimage of fullNode root: %v", rootHash))

	// save only these into a validator trie
	subTriePreimages := make(map[common.Hash][]byte)
	subTriePreimages[rootHash] = valInput.Preimages[0][rootHash]
	log.Println(fmt.Sprintf("[Init] Number of preimages in the subtrie: %v", len(subTrieHashes) + 1))
	for _, pi := range subTrieHashes {
		_, exists := valInput.Preimages[0][pi]
		if !exists { panic(fmt.Sprintf("TrieFromNode selected a pre-image that isn't in valnput: %v", pi)) }
		subTriePreimages[pi] = valInput.Preimages[0][pi]
	}

	initCacheUpdate := &trie.CacheUpdate{
						NodesAccessed: []common.Hash{},
						NodesChanged: []common.Hash{},
						NodesAdded: []common.Hash{},
						NodesDeleted: []common.Hash{},
					}

	cacheSubTrie = &trie.ValidatorTrie{
					Root: n,
					Nodes: subTriePreimages,
					Pathmap: make(map[string]common.Hash),
					NodesChangedAndLost: make(map[common.Hash][]byte),
					NodesChangedAndLostPrefix: make(map[common.Hash][]byte),
					LostNodePrevHash: make(map[common.Hash][]byte),
					LostNodePrevHashPrefix: make(map[common.Hash][]byte),
					Mutex: &sync.RWMutex{},
					NumDeletes: 0,
					TrieKeys: make(map[common.Hash][]byte),
					KeyToHash: make(map[common.Hash]common.Hash),
					LastUpdate: initCacheUpdate,
					PrefixesOfInterest: []byte{},
	}
	//ok := cacheSubTrie.InitPathmap()
	cacheSubTrie.TrieCreateKeyMap()
	nilHash := trie.HashTrieKey([]byte{})
	cacheSubTrie.LastUpdate.KeyAdd([]byte{})
	cacheSubTrie.LastUpdate.AddAccess([]byte{})
	_, exists = cacheSubTrie.TrieKeys[common.BytesToHash(nilHash)]
	if exists {
		panic("Root hash already added")
	}
	cacheSubTrie.TrieKeys[common.BytesToHash(nilHash)] = valInput.Preimages[0][rootHash]
	log.Println("Number in prefix map", len(cacheSubTrie.TrieKeys))
	keys := []common.Hash{}
	for k, _ := range(cacheSubTrie.TrieKeys) {
		keys = append(keys, k)
	}
	//log.Println("trie keys", keys)
	//log.Println("update keys", cacheSubTrie.LastUpdate.NodesAdded)
	keysNotInUpdate := l1NotInl2(keys, cacheSubTrie.LastUpdate.NodesAdded)
	updateNotInKeys := l1NotInl2(cacheSubTrie.LastUpdate.NodesAdded, keys)
	log.Println("Nodes in triekeys not in update", keysNotInUpdate)
	log.Println("Nodes in update not in triekeys", updateNotInKeys)

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
	rootNodeRaw := valInput.Preimages[0][blockHeader.Root]
	rootNode, _ := trie.PublicDecodeNode(nil, rootNodeRaw)
	//rootNode, _ := trie.PublicDecodeNode(blockHeader.Root.Bytes(), rootNodeRaw)

	// see if the cache subtrie root exists in this request
	newRoot, ok := trie.NodeFromPath(rootNode, pathToSubTrieRoot, valInput.Preimages[0])
	// TODO: newRoot, ok := trie.TrieNodeFromPrefix(rootNode, cacheSubTriePrefix,  
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
			//success := cacheSubTrie.TrieUpdate(newRoot, valInput.Preimages[0])
			success := cacheSubTrie.TrieUpdatePrefix(newRoot, valInput.Preimages[0])
			if !success {
				log.Println("Couldn't update the cache trie")
				return false
			} else {
				log.Println("Successfully updated the cache trie")
				// reset the trie root
				cacheSubTrie.Root = newRoot
				log.Println(fmt.Sprintf("New Root. Hash=%v, Node=%v", trie.HashNode(newRoot), newRoot))
				//numNodes := cacheSubTrie.NumNodesWithStorage()
				numNodes := cacheSubTrie.NumNodesWithStoragePrefix()
				//tHash := trie.TrieFromNode(cacheSubTrie.Root, cacheSubTrie.Nodes)
				d := cacheSubTrie.NumDeletes
				log.Println("Nodes in trie AFTER update:", numNodes)
				//log.Println("Hashes in trie", len(tHash))
				log.Println("num Deleted", d)
				cacheSubTrie.NumDeletes = 0
				//log.Println("Number preimages:", len(cacheSubTrie.Nodes))
				log.Println("Number preimages:", len(cacheSubTrie.TrieKeys))
				//size := cacheSubTrie.SizeInBytesWithStorage()
				//log.Println("Size of trie AFTER update:", size)
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

var numFilesProcess = 1
//var numInputsProcess = 3565
var numInputsProcess = 10000000
//var numInputsProcess = 3467
// [6 7 3 7 11 -1 8 15 8 2 10 14]
// INFO [04-11|13:42:56.979] the Node        n="{02000c040408030504000d060403070e020704020a0f03050a010b03000b0605020c0c080901030d0d0c08060e0b0a0705040106080d0907070610: 837a873c } "
//var numInputsProcess = 538
// This function reads SAVED validation inputs and processes them normally
// As opposed to func validate(..) which is called when an input is received from a client

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
	numProcessed := 0
	finalFile := ""
	for _, v := range files { 
		//if numProcessed < numFilesProcess {
		if true {
			finalFile = v.Name()
			//numProcessed = numProcessed + 1
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
			//bound := startId
			//if endId <= startId + numInputsProcess {
			//	bound = endId
			//} else {
			//	bound = startId + numInputsProcess
			//}

			//for i := startId; i <= bound; i++ {
			for i := startId; i <= endId; i++ {
				// get valInput from the file
				if numProcessed > numInputsProcess {
					break 
				}
				numProcessed = numProcessed + 1
				err = dec.Decode(&vinput)
				if err != nil {
					panic(err)
				}
				processInput(&vinput)
				// TODO: debug vvv
				//break
			}
			f.Close()
			if numProcessed > numInputsProcess {
				break
			}
		} else {
			break
		}
	}
	
	//numNodes := cacheSubTrie.NumNodesWithStorage()
	//sRoots := trie.NumStorageRoots(cacheSubTrie.Root, cacheSubTrie.Nodes)
	//log.Println("Nodes in trie AFTER update:", numNodes)
	tHash := trie.TrieFromNodePrefixDebug(cacheSubTrie.Root, cacheSubTrie.TrieKeys, cacheSubTrie.NodesChangedAndLostPrefix, []byte{})
	//tHash = append(tHash, trie.HashNode(cacheSubTrie.Root))
	rootKeyHash := common.BytesToHash(trie.HashTrieKey([]byte{}))
	tHash = append(tHash, rootKeyHash)
	for x, i := range tHash {
		for y, j := range tHash {
			if i == j && x != y {
				log.Println("duplicate", i)
			}
		}
	}
	// Trie from node as map
	tMap := make(map[common.Hash]bool)
	log.Println("hashes from trie", len(tHash))
	for _, k := range tHash {
		tMap[k] = true
	}
	
	//for k := range cacheSubTrie.NodesChangedAndLost {
	//	_, exists := cacheSubTrie.Nodes[k]
	//	if exists {
	//		//panic("Node is in BOTH")
	//	}
	//}
	
	finalNodeMap := make(map[common.Hash][]byte)
	//for k := range cacheSubTrie.Nodes {
	//	finalNodeMap[k] = cacheSubTrie.Nodes[k]
	//}
	for k := range cacheSubTrie.TrieKeys {
		finalNodeMap[k] = cacheSubTrie.TrieKeys[k]
	}
	//for k := range cacheSubTrie.NodesChangedAndLost {
	//	finalNodeMap[k] = cacheSubTrie.NodesChangedAndLost[k]
	//}
	for k := range cacheSubTrie.NodesChangedAndLostPrefix {
		finalNodeMap[k] = cacheSubTrie.NodesChangedAndLostPrefix[k]
	}
	log.Println("Number preimages:", len(finalNodeMap))

	//log.Println("lost", len(cacheSubTrie.NodesChangedAndLost))
	//for k,v := range cacheSubTrie.NodesChangedAndLost {
	//	log.Println("Key", k)
	//	n, err := trie.PublicDecodeNode(k.Bytes(), v)
	//	if err != nil {
	//		panic("fucked")
	//	} else {
	//		log.Println("Node", n)
	//	}
	//}
	diff := []common.Hash{}
	if len(tMap) > len(finalNodeMap) {
		log.Println("trieFromNode > trieKeys")
		for k := range tMap {
			_, exists := finalNodeMap[k]
			if !exists {
				//_, exists := cacheSubTrie.NodesChangedAndLost[k]
				//if !exists {
				diff = append(diff, k)
				//}
			}
		}
		log.Println("in trieFromNode not in TrieKeys", diff)
		for _,d := range diff {
			_, exists := cacheSubTrie.NodesChangedAndLostPrefix[d]
			if exists {
				log.Println(fmt.Sprintf("Diff item %v in Lost", d))
			}
		}
		otherDiff := []common.Hash{}
		for k := range finalNodeMap {
			_, exists := tMap[k]
			if !exists {
				otherDiff = append(otherDiff,k)
			}
		}
		log.Println("IN TrieKeys not in trieFromNode", otherDiff)
	} else {
		log.Println("trieFromNode < trieKeys")
		for k := range finalNodeMap { //cacheSubTrie.Nodes {
			_, exists := tMap[k]
			if !exists {
				diff = append(diff, k)
			}
		}
		log.Println("diff", diff)
	}
	//cacheSubTrie.NumChildrenExist(cacheSubTrie.Root)
	for _, d := range diff {
		_, exists := cacheSubTrie.NodesChangedAndLost[d]
		if exists {
			log.Println("Node is lost", d)
		}
		//if i < 3324234234 {
		//	raw := cacheSubTrie.Nodes[d]
		//	n, err := trie.PublicDecodeNode(d.Bytes(), raw)
		//	if err == nil {
		//		log.Println(fmt.Sprintf("\nDiff=%v \nnode=%v", d, n))
		//	} else {
		//		panic("couldn't decode")
		//	}
		//}
	}
	inTrieNotInKeys := []common.Hash{}
	for k := range tMap {
		_, exists := finalNodeMap[k]
		if !exists {
			inTrieNotInKeys = append(inTrieNotInKeys, k)
		}
	}

	inKeysNotInTrie := []common.Hash{}
	for k := range finalNodeMap {
		_, exists := tMap[k]
		if !exists {
			inKeysNotInTrie = append(inKeysNotInTrie, k)
		}
	}
	log.Println("inTrieNotInKeys", inTrieNotInKeys)
	log.Println("inKeysNotInTrie", inKeysNotInTrie)
	//n, exists := trie.NodeFromPath(cacheSubTrie.Root, []int{5}, finalNodeMap)
	//if exists {
	//	log.Println("node from path [5]", n)
	//} else {
	//	log.Println("no node")
	//}
	//n, exists = trie.NodeFromPath(cacheSubTrie.Root, []int{}, finalNodeMap)
	//if exists {
	//	log.Println("node from path []", n)
	//	log.Println("hash", trie.HashNode(n))
	//	_, exists = tMap[trie.HashNode(n)]
	//	log.Println("in thash", exists)
	//} else {
	//	log.Println("no node")
	//}
	//if numNodes != len(tHash) {
	//	panic(fmt.Sprintf("Trie from root gave %v but NumNodes gives %v, storage roots=%v", len(tHash), numNodes, sRoots))
	//}
	d.Close()
	log.Print(fmt.Sprintf("Processed files from %v to %v", files[0].Name(), finalFile))


	// get the key
	//fullKey := cacheSubTrie.ReturnFullKey(cacheSubTrie.Root, []int{5, 7, 6, 14, 14})
	//log.Println(fmt.Sprintf("fullKey: %x", fullKey))
	//log.Println("Length of key", len(fullKey))
	//log.Println(fmt.Sprintf("%x", trie.PublicHexToKeybytes(fullKey)))

	return true
}

// DEBUG function to search for specific preimages in the saved data
func findPreimageInFiles() {
	//preimage := common.HexToHash("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")
	//preimage := common.HexToHash("3b44b8c856a5f7ad22d92bb8a05b9a1d3cde48edaebdd4b73d229ad01709f7cc")
	//preimage := common.HexToHash("999b74ef968b5eaacc643dea0722e18fb8f0b533e4b091e203aa863d464da227")
	preimage := common.HexToHash("6bb4949ca18080d565d4549a8daabe75586aae53b7601b270c08d96860368c11")
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
			_, exists := vinput.Preimages[0][preimage]
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
		rootNodeRaw := valInput.Preimages[0][blockHeader.Root]
		rootNode, _ := trie.PublicDecodeNode(nil, rootNodeRaw)
		//rootNode, _ := trie.PublicDecodeNode(blockHeader.Root.Bytes(), rootNodeRaw)

		// just checks that our cache is created correctly, our hashing is done correctly
		// check that if we run `NodeHashFromPath` with the path chosen above that we arrive at the same hash
		rootHashFromPath, exists := trie.NodeHashFromPath(rootNode, pathToSubTrieRoot, valInput.Preimages[0])
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

		// initialize 
		cache = &TestCache{
					trie: cacheSubTrie,
					//contents: append([]common.Hash{}, (cacheSubTrie.LastUpdate.NodesAdded)...),
					//contents: []common.Hash{},
					//fifo: []uint8{},
					hashToIdx: make(map[common.Hash]int, cacheSize),
					contents: make([]common.Hash, cacheSize),
					//fifo: make(map[common.Hash]uint8, cacheSize),
					fifo: make([]uint8, cacheSize),
					pointer: 0,
		}

		//cache.Update(cacheSubTrie.LastUpdate)

		// get node from path

		/////////// DEBUG AND TEST GETTING BY PREFIX ////////////////////
		//sn1key, _ := hex.DecodeString("05050205010403010a07060f020f0e0d000002020800000f02000d020604080d0f0b050b0208000f090a0b070a030c0b0206070f000d0101090210")
		//sn2key , _ := hex.DecodeString("09000d0e0c0d090504080b06020a080d06000304050a0908080308060f0c08040b0a060b0c09050408040000080f060306020f09030106000e0f030e05060310")
		//npath, exists := trie.NodeFromPath(cacheSubTrie.Root, []int{5, 7, 6, 14, 14, -1, 2}, valInput.Preimages[0])
		//fullPrefix := []byte{5, 7, 6, 14, 14}		// up to the short node
		//fullPrefix = append(fullPrefix, sn1key...)	// the value node
		//fullPrefix = append(fullPrefix, byte(1))	// storage trie root
		//fullPrefix = append(fullPrefix, byte(2))	// final short node
		//fullPrefix = append(fullPrefix, sn2key...)	// valueNode
		//nprefix, ok := cacheSubTrie.NodeFromPrefix(fullPrefix)
		//if !exists {
		//	log.Println(fmt.Sprintf("npath doesn' exist"))
		//} 
		//if !ok {
		//	log.Println(fmt.Sprintf("nprefix doesn't exist. Prefx=%x", []byte{5,7}))
		//}
		//log.Println("Path node", npath)
		//log.Println("Prefix node", nprefix)
		// reset the LastUpdate
		cacheSubTrie.LastUpdate = &trie.CacheUpdate{
									NodesChanged: []common.Hash{},
									NodesAdded: []common.Hash{},
									NodesDeleted: []common.Hash{},
		}
		//panic("dick")
		/////////// DEBUG AND TEST GETTING BY PREFIX ////////////////////
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
				panic("Collection mode is wrong we shouldn't have out of order inputs rn")
			} else {
				// process this one because it's next
			    ok := processValidationInput(valInput)
				if !ok {
					log.Println(fmt.Sprintf("Couldn't propoerly update the cache"))
				}
				//cache.Update(cacheSubTrie.LastUpdate)
				//log.Println("Cache hastToIdx size:", len(cache.hashToIdx))
				//keysInTrie := []common.Hash{}
				//for k, _ := range cacheSubTrie.TrieKeys  {
				//	keysInTrie = append(keysInTrie, k)
				//}
				//for k, _ := range cacheSubTrie.NodesChangedAndLostPrefix {
				//	keysInTrie = append(keysInTrie, k)
				//}
				//keysInCache := []common.Hash{}
				//for k, _ := range cache.hashToIdx {
				//	keysInCache = append(keysInCache, k)
				//}
				//inTrieNotInCache := l1NotInl2(keysInTrie, keysInCache)
				//log.Println("Hashes in trie not in cache", inTrieNotInCache)
				//inCacheNotInTrie := l1NotInl2(keysInCache, keysInTrie)
				//log.Println("Hashes in cache not in trie", inCacheNotInTrie)
				cacheSubTrie.LastUpdate = &trie.CacheUpdate{
											NodesChanged: []common.Hash{},
											NodesAdded: []common.Hash{},
											NodesDeleted: []common.Hash{},
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
						target := common.HexToHash("0x43855364b4a20a9c6d82e9096e6c742b31d63166d4fdf8cc57056f7e1b5b4540")
						for _, k := range cacheSubTrie.LastUpdate.NodesAdded {
							if k == target {
								log.Println("The hash exists in NodesAdded")
							}
						}
						//cache.Update(cacheSubTrie.LastUpdate)
						//log.Println("Cache hastToIdx size:", len(cache.hashToIdx))
						lastInputNumber = inp.Id
						delete(bufferedValidations, inp.Id)
						// reset the LastUpdate
						cacheSubTrie.LastUpdate = &trie.CacheUpdate{
													NodesChanged: []common.Hash{},
													NodesAdded: []common.Hash{},
													NodesDeleted: []common.Hash{},
						}
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
	//if (numSuccessfulValidations % 100 == 1) {
	log.Println(fmt.Sprintf("Validated %v requests.", numSuccessfulValidations))
	//}
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
		if numSaved <= 400000 {
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

func (a *ValidationServerAPI) StylusArchs() ([]ethdb.WasmTarget, error) {
	return a.spawner.StylusArchs(), nil
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

func (a *ExecServerAPI) GetMachineHashesWithStepSize(ctx context.Context, execid, fromStep, stepSize, maxIterations uint64) ([]common.Hash, error) {
	run, err := a.getRun(execid)
	if err != nil {
		return nil, err
	}
	hashesInRange := run.GetMachineHashesWithStepSize(fromStep, stepSize, maxIterations)
	res, err := hashesInRange.Await(ctx)
	if err != nil {
		return nil, err
	}
	return res, nil
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
