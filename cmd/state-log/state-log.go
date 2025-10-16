package main

import (
	"math"
	_ "encoding/json"
	_ "fmt"
	_ "io/ioutil"
	_"math/big"
	"os"
	_ "reflect"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/trie"
)

func CheckRoot(obj state.Log) bool {
	_, ok := obj.ANodes()[obj.RootHash()]
	if !ok {
		return false
	}

	return true
}

func ExploreTrie(obj state.Log) ([]common.Hash, bool) {
	rootRaw, ok := obj.ANodes()[obj.RootHash()]
	log.Info("Root", "roothash", obj.RootHash())
	if !ok {
		//log.Info("Log", "accounts", len(obj.AccountsSeen()), "Anodes", obj.AccountsSeen())

		// panic("Root isn't in nodes")
		return nil, false
	}
	root, err := trie.PublicDecodeNode(nil, rootRaw)
	if err != nil {
		log.Error("COuldn't decode pre root")
		panic(err)
	}
	testMap := MergeMaps(obj.ANodes(), obj.KNodes())
	count := trie.TrieFromNodeCountAccounts(root, testMap, []byte{})
	return count, true
}

// func ExploreTrieKeys(obj state.Log) (map[common.Hash][]common.Hash, bool) {
func ExploreTrieKeys(obj state.Log) (map[common.Hash][]common.Hash, bool) {
	rootRaw, ok := obj.ANodes()[obj.RootHash()]
	log.Info("Root", "roothash", obj.RootHash())
	if !ok {
		log.Debug("Log", "accounts", len(obj.AccountsSeen()), "Anodes", obj.AccountsSeen())

		// panic("Root isn't in nodes")
		return nil, false
	}
	root, err := trie.PublicDecodeNode(nil, rootRaw)
	if err != nil {
		log.Error("COuldn't decode pre root")
		panic(err)
	}
	testMap := MergeMaps(obj.ANodes(), obj.KNodes())
	var emptyHash common.Hash
	emptyHash.SetBytes(nil)
	count := trie.TrieFromNodeCountKeys(root, testMap, []byte{}, emptyHash, false)
	return count, true
}

func ExploreTrieAllHashes(obj state.Log) (map[common.Hash]map[common.Hash][]byte, bool) {
	rootRaw, ok := obj.ANodes()[obj.RootHash()]
	log.Info("Root", "roothash", obj.RootHash())
	if !ok {
		log.Debug("Log", "accounts", len(obj.AccountsSeen()), "Anodes", obj.AccountsSeen())

		// panic("Root isn't in nodes")
		return nil, false
	}
	root, err := trie.PublicDecodeNode(nil, rootRaw)
	if err != nil {
		log.Error("COuldn't decode pre root")
		panic(err)
	}
	testMap := MergeMaps(obj.ANodes(), obj.KNodes())
	var emptyHash common.Hash
	emptyHash.SetBytes(nil)
	count := trie.TrieFromNodeHashDuplicates(root, testMap, []byte{})
	return count, true
}

func ValidatorTrieFromObj(obj state.Log) *trie.ValidatorTrie {
	rootRaw, ok := obj.ANodes()[obj.RootHash()]
	if !ok {
		panic("Root isn't in nodes")
	}
	root, err := trie.PublicDecodeNode(nil, rootRaw)
	if err != nil {
		log.Error("Couldn't decode pre root")
		panic(err)
	}
	allNodes := MergeMaps(obj.ANodes(), obj.KNodes())
	return &trie.ValidatorTrie{
		Root:  root,
		Nodes: allNodes,
	}
}

func ExploreTarget(target common.Address, preObj *state.PreLog, postObj *state.PostLog) bool {
	if ignoreJournal(preObj.Journals) {
		log.Info("An empty journal is valid.")
		return true
	}

	// Basically go through the trie and log all the changes that happen
	// log which nodes "changed" and which nodes were deleted or added
	// TODO: the purpose of this function was to track all the changes for a spceific account
	// 		and make sure that we could recreate all of them just be looking at the trie of stored hashes and nodes

	return false
}

var LOGDIR string = "/home/admin/statedb-data-old"

func validationMain(logDir string) {
	CheckPostDataLogsEverything(logDir)
}

func simMain(logDir string) {
	s := NewLRUSim(5000)
	//s.Run(logDir)
	//s.RunRecordTxBytes(logDir)
	s.RunRecordBlockBytes(logDir, 10000)
}

func concurrentMain(logDir string) {
	//SimInfiniteCores(logDir, 10000)
	//SimInfiniteCoresSpeedup(logDir, 10000)
	//SimInfiniteCoresFromFile(logDir, "/home/admin/surya/nitro/block-access-100000.data")
	//SimFiniteCores(logDir, 4,  30000)
	//SimFiniteCores(logDir, 8,  30000)
	//SimFiniteCoresSpeedup(logDir, 4, 1000)
	//SimFiniteCoresSpeedup(logDir, 8, 30000)
	//SimMultipleFiniteCores(logDir, []int{2, 4, 8, 16}, 10000)
	//SimMultipleFiniteCoresFromFile(logDir, "/home/admin/surya/nitro/block-access-100000.data", []int{2, 4, 8, 16})
	//CheckSameGraphFileAndLive(logDir, "/home/admin/surya/nitro/block-access.data", 1000)
	//CompareSpecificBlock(logDir, "/home/admin/surya/nitro/block-access.data", 1000, 359791948)
	SimMultipleGroupBlocks(logDir, "/home/admin/surya/nitro/block-access-100000.data", []int{2, 4, 8, 16}, 2)
}

func main() {
	log.SetDefault(log.NewLogger(log.NewTerminalHandlerWithLevel(os.Stderr, log.LevelDebug, true)))

	//validateMain(LOGDIR)
	//simMain(LOGDIR)
	concurrentMain(LOGDIR)
	//investigateBlock(LOGDIR, 359791727)
	//WriteBlockAccessesToFile(LOGDIR, 100000, "/home/admin/surya/nitro/block-access-100000.data")
	//WriteBlockAccessesToFile(LOGDIR, math.MaxInt, "/home/admin/surya/nitro")
	//ValidateBlockAccessesFile(LOGDIR, 30000, "/home/admin/surya/nitro/block-access.data")
	//CheckSameBlocksWritten(LOGDIR, 1000)

	//first, last := getDataBlockRange(LOGDIR)
	//log.Info("Blocks collected", "first", first, "last", last)
	//getNumTxsInNBlocks(10, LOGDIR)
	return

	// get all the pre and post data for block 0
	//one := big.NewInt(1)
	//blockNo := big.NewInt(0)
	blockNo := 0
	version := 1

	done := false
	noMoreVersions := false
	prevRoot := types.EmptyCodeHash

	for {
		for {
			content, err := readPre(blockNo, version)
			if err != nil {
				log.Error("No pre file", "e", err, "version", version)
				if noMoreVersions {
					done = true
				} else {
					noMoreVersions = true
				}
				break
			}
			preObj := preFromBytes(content)
			samplePreData(preObj)

			// assert that this preLog's root is the same a the last PostLog
			if prevRoot.Cmp(types.EmptyCodeHash) != 0 {
				if prevRoot.Cmp(preObj.Root) != 0 {
					log.Error("Log hashes", "preLog(n)", preObj.Root, "postLog(n-1)", prevRoot)
					panic("Prelog doesn' thave the same hash as the previous postLog")
				} else {
					log.Info("The hashes in preLog(n) and postLog(n-1) are consistent. YAY!")
				}
			}

			content, err = readPost(blockNo, version)
			if err != nil {
				log.Error("No post file", "e", err, "version", version)
				if noMoreVersions {
					done = true
				} else {
					noMoreVersions = true
				}
				break
			}

			postObj := postFromBytes(content)
			// print out some of the data, passes visual inspection
			samplePostData(postObj)
			prevRoot = postObj.Root

			// state.PrintJournal(preObj.Journals)

			success := validatePrePost(preObj, postObj)
			if !success {
				panic("")
			}
			version++
			if noMoreVersions {
				noMoreVersions = false
			}
			// accesses := GetAccessOrder(preObj, postObj)
			// log.Info("Accesses", "l", accesses)
			// done = true
			//break
		}
		if done {
			break
		}
		if noMoreVersions {
			//blockNo.Add(blockNo, one)
			blockNo++
			version = 1
			log.Info("Next block", "b", blockNo)
		}
	}

	log.Info("Done processing data.")

	// postcount = ExploreTrie(postObj)
	// log.Info("Post count", "c", count)

	// create the full set of preimages

}

func checkPreLogRoot(preObj *state.PreLog, prevRoot common.Hash) bool {
	// assert that this preLog's root is the same a the last PostLog
	if prevRoot.Cmp(types.EmptyCodeHash) != 0 {
		if prevRoot.Cmp(preObj.Root) != 0 {
			log.Error("Log hashes", "preLog(n)", preObj.Root, "postLog(n-1)", prevRoot)
			return false
		} else {
			log.Info("The hashes in preLog(n) and postLog(n-1) are consistent. YAY!")
		}
	}
	return true
}

//func ProcessLogs() {
//	//one := big.NewInt(1)
//	//blockNo := big.NewInt(0)
//	blockNo := 0
//	version := 1
//
//	done := false
//	noMoreVersions := false
//	prevRoot := types.EmptyCodeHash
//
//	for { // for each block
//		for { // for each log file in that block
//			// read preLog and log everything
//			preObj, _, exists := getPrePostObjs(blockNo, version)
//			if !exists {
//				if noMoreVersions {
//					done = true
//				} else {
//					noMoreVersions = true
//				}
//			}
//
//			// assert that the preLog's root is the same as the last postLog
//			if !checkPreLogRoot(preObj, prevRoot) {
//				panic("Prelog doesn' thave the same hash as the previous postLog")
//			}
//			validatePreLog(preObj)
//			done = true
//			break
//			// samplePostData(postObj)
//
//			// add the preLog accesses
//
//			// log.Info("Pre accesses", "l", len(preAccesses))
//
//			// consume upto and including all logs where
//			// process the postLogs in the order of the journal with the updated nodes
//
//			break
//		}
//		if done {
//			break
//		}
//		if noMoreVersions {
//			//blockNo.Add(blockNo, one)
//			blockNo++
//			version = 1
//			log.Info("Next block", "b", blockNo)
//		}
//	}
//
//}

/*

Now we actually try to do cache management and the related functions with this data.
When something is deleted or added to the state trie, this results in paths to other keys also changing.
In order to do cache management, we need to know which trie nodes became new nodes because a value within them changed, and which nodes are completely new.
When traversing the trie:

FullNode:
If the old and new tries have the same fullNode with at least one matching child (empty entries count as matching children) then this fullNode is modified with some new hash.
If a shortNode is seen where a fullNode used to be, that means the keys in this subtrie that divided on one value, are now combined into a new value

*/

func GetAccessOrder(preObj *state.PreLog, postObj *state.PostLog) []common.Hash {
	t := ValidatorTrieFromObj(preObj)
	// accesses := state.OrderAccesses(preObj.Journals, t)
	accesses := state.OrderAccessesReverse(preObj.Journals, preObj.Root, preObj.Accounts, preObj.AccountNodes, preObj.Keys, preObj.KeyNodes, t)
	return accesses
}

// func GetAccessOrder(journals [][]state.LogJournalEntry, t *trie.ValidatorTrie) []common.Hash {
//	return state.OrderAccesses(journals, t)
//}
