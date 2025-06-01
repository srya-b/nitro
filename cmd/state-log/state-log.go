package main

import (
	"os"
	"fmt"
	"io/ioutil"
	"encoding/json"
	"math/big"
	"reflect"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/trie"
)

var logDir string = "/home/sbakshi/arb1/arb-devnode/state-logs"

func readPre(b *big.Int, v int) ([]byte, error) {
	fn := fmt.Sprintf("%s/predata-%v-%d.json", logDir, b, v)
	log.Info("Getting Pre", "fn", fn)
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

func readPost(b *big.Int, v int) ([]byte, error) {
	fn := fmt.Sprintf("%s/postdata-%v-%d.json", logDir, b, v)
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

func MergeMaps[K comparable, V any](map1 map[K]V, map2 map[K]V) map[K]V {
	testMap := make(map[K]V)
	for hn, raw := range map1 {
		testMap[hn] = raw
	}
	for hn, raw := range map2 {
		testMap[hn] = raw
	}
	return testMap
}

func ExploreTrie(obj state.Log) []common.Hash {
	rootRaw, ok := obj.ANodes()[obj.RootHash()]
	log.Info("Root", "roothash", obj.RootHash())
	if !ok {
		panic("Root isn't in nodes")
	}
	root, err := trie.PublicDecodeNode(nil, rootRaw)
	if err != nil {
		log.Error("COuldn't decode pre root")
		panic(err)
	}
	testMap := MergeMaps(obj.ANodes(), obj.KNodes())
	count := trie.TrieFromNodeCountKeys(root, testMap, []byte{})
	return count
}

func listToMap[K comparable](l []K) map[K]bool {
	out := make(map[K]bool)
	for _, e := range l {
		out[e] = true	
	}
	return out
}

func mapToSet[K comparable, V any](m map[K]V) map[K]bool {
	out := make(map[K]bool)
	for k := range m {
		out[k] = true
	}
	return out
}

func listToSet[K comparable](l []K) map[K]bool {
	out := make(map[K]bool)
	for _, e := range l {
		out[e] = true
	}
	return out
}

func samplePostData(postObj *state.PostLog) {
	i := 0
	log.Info("Read post data", "root", postObj.Root)
	for addr, paths := range postObj.Accounts {
		if i > 4 {
			break 
		}
		log.Info("data", "account", addr, "paths", len(paths))
	}
}

func ignoreJournal(j [][]state.LogJournalEntry) bool {
	for _, jn := range j {
		if len(jn) > 0 {
			return false
		}
	}
	return true
}

func samplePreData(preObj *state.PreLog) {
	if len(preObj.Journals) > 0 {
		log.Info("Read pre data", "root", preObj.Root, "data", preObj.Journals[0][0:min(4, len(preObj.Journals[0]))])
	} else {
		log.Info("Journal is empty")
	}
	log.Info("Emptys", "list", preObj.EmptyDeletes)
}

func mapSubtract[K comparable, V comparable](m map[K]V, subtract map[K]V) map[K]V {
	out := make(map[K]V)
	for k := range m {
		_, ok := subtract[k]
		if !ok {
			out[k] = m[k]
		} else {
			mv, _ := m[k]
			subv, _ := subtract[k]
			if subv != mv {
				panic("Keys don't have the same valuie")
			}
		}
	}
	return out
}

func hashAddressSet(m map[common.Address]bool) map[common.Hash]bool {
	out := make(map[common.Hash]bool)
	for addr := range m {
		out[common.BytesToHash(trie.PublicHashKey(addr.Bytes()))] = m[addr]
		log.Info("Preimage", "addr", addr, "hash", common.BytesToHash(trie.PublicHashKey(addr.Bytes())))
	}
	return out
}

func validatePreLog(preObj *state.PreLog) bool {
	// check that the trie finds all the accounts in the trie
	// get all accounts found by the trie (hashed keys)
	if ignoreJournal(preObj.Journals) {
		log.Info("An empty journal is valid.")
		return true
	}

	preKeys := ExploreTrie(preObj)
	accountsFound := listToSet(preKeys)

	// all the accounts that were created (unhashed) from the Journal
	createdAccounts := state.GetCreatedAccounts(preObj.Journals)

	// the accounts in the trie in objects
	//accountsInTrie := make(map[common.Hash]bool)
	accountsInTrie := hashAddressSet(mapSubtract(mapToSet(preObj.Accounts), createdAccounts))

	eq := reflect.DeepEqual(accountsFound, accountsInTrie)
	if eq {
		log.Info("Equal found and in journal")
		return true
	} else {
		log.Error("Differing", "accountsFound", accountsFound, "accountsInTrie", accountsInTrie)
		return false
	}
}

// Checks that the accounts reachable by traversing the saved hashes is the same
// as the set if reading from the journal of this block. It's good validation
// that the data collected is complete.
func validatePrePost(preObj *state.PreLog, postObj *state.PostLog) bool {

	// Go through the journal and determine which accounts already existed before this block
	// and check that the same accounts are found when the trie encoded by the node hashes is 
	// traversed.
	if ignoreJournal(preObj.Journals) {
		log.Info("An empty journal is valid.")
		return true
	}

	preKeys := ExploreTrie(preObj)
	accountsFound := listToSet(preKeys)

	createdAccounts := state.GetCreatedAccounts(preObj.Journals)
	deletedAccounts := state.GetDeletedAccounts(preObj.Journals)
	emptyDeletes := GetEmptys(preObj)
	// the deleted accounts including the ones that were deleted without a self destruct
	// because they were empty when finalize was called
	realDeletes := MergeMaps(deletedAccounts, emptyDeletes)

	// traverse the trie from the hashes and get all the Hash(address) keys that are reached
	accountsInTrie := hashAddressSet(mapSubtract(mapToSet(preObj.Accounts), createdAccounts))

	eq := reflect.DeepEqual(accountsFound, accountsInTrie)
	if !eq {
		log.Error("Differing", "accountsFound", accountsFound, "accountsInTrie", accountsInTrie)
		return false
	}

	// Process the post data and check that the trie encoded by the hashes in the post log
	// include all of the deleted accounts from the pre data and all the newly created accounts
	// read from the journal
	postKeys := ExploreTrie(postObj)
	accountsFound = listToSet(postKeys)

	// all preObj.Accounts should be in here
	accountsInPre := hashAddressSet(mapSubtract(mapToSet(preObj.Accounts), realDeletes))
	eq = reflect.DeepEqual(accountsFound, accountsInPre)
	if !eq {
		log.Error("the two maps", "accountsInPre", accountsInPre, "accountsFound", accountsFound)
		panic("not equal")
	} 
	
	log.Info("We all good")
	return true
}

// the real key here is that something might be deletd because it's empty in
//one block and then is created again in the next block. We need to make sure
//that things that eventually end up existing aren't returned in this map.
func GetEmptys(preObj *state.PreLog) map[common.Address]bool {
	// there should always be as many journals as there are empty slices
	created := state.GetEmptyDeletes(preObj.EmptyDeletes, preObj.Journals)

	return created
}


func main() {
	log.SetDefault(log.NewLogger(log.NewTerminalHandlerWithLevel(os.Stderr, log.LevelInfo, true)))

	// get all the pre and post data for block 0
	one := big.NewInt(1)
	blockNo := big.NewInt(0)
	version := 1

	for {	
		done := false
		for {
			content, err := readPre(blockNo, version)
			if err != nil {
				log.Error("Error on pre", "e", err, "version", version)
				done = true
				break	
			}
			preObj := preFromBytes(content)
			samplePreData(preObj)

			content, err = readPost(blockNo, version)
			if err != nil {
				log.Error("Error on post", "e", err, "version", version)
				done = true
				break	
			}
			postObj := postFromBytes(content)
			// print out some of the data, passes visual inspection
			samplePostData(postObj)

			state.PrintJournal(preObj.Journals)

			validatePrePost(preObj, postObj)
			version++
		}
		if done {
			break 
		}
		blockNo.Add(blockNo, one)
	}


	//postcount = ExploreTrie(postObj)
	//log.Info("Post count", "c", count)

	// validate the post data and see that all the created accounts are now in the trie
	// and the set is complete

}

