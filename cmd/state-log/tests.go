package main

import (
	"math/big"
	"reflect"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/state"
	_ "github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/trie"
	_ "github.com/ethereum/go-ethereum/trie"
)

func CheckPostDataLogsEverything() {
	blockno := big.NewInt(0)

	preObj, exists := getPreObj(blockno, 1)
	if !exists {
		log.Error("FIrst prelog should exists")
		panic("Read preloog error")
	}

	postObj, exists := getPostObj(blockno, 1)
	if !exists {
		log.Error("Last post log version 2 should be there")
		panic("Read post log error")
	}

	validatePreLog(preObj)
	validatePostLog(postObj)

	ExploreTrieKeys(preObj)
}

func validatePreLog(preObj *state.PreLog) bool {
	// check that the trie finds all the accounts in the trie
	// get all accounts found by the trie (hashed keys)
	if ignoreJournal(preObj.Journals) {
		log.Info("An empty journal is valid.")
		return true
	}

	// preKeys, _ := ExploreTrie(preObj)
	// accountsFound := listToSet(preKeys)

	// all the accounts that were created (unhashed) from the Journal
	createdAccounts := state.GetCreatedAccounts(preObj.Journals)
	deletedAccounts := state.GetDeletedAccounts(preObj.Journals)
	emptyDeletes := GetEmptys(preObj)
	realAccountDeletes := MergeMaps(deletedAccounts, emptyDeletes)

	createdKeys := state.GetCreatedKeys(preObj.Journals)
	zeroGets := state.GetKeysAlwaysZero(preObj.Journals)
	deletedKeys := state.GetDeletedKeys(preObj.Journals)

	// the accounts in the trie in objects
	// accountsInTrie := make(map[common.Hash]bool)
	accountsInTrie := hashAddressSet(mapSubtract(mapToSet(preObj.Accounts), createdAccounts))
	keysInTrie := mapSubtract(mapToSet(preObj.Keys), createdKeys)
	keysInTrie = mapSubtract(keysInTrie, zeroGets)

	log.Info("Accounts in Trie", "map", accountsInTrie)
	log.Info("Created accounts", "map", hashAddressSet(createdAccounts))
	log.Info("Deleted accounts", "map", hashAddressSet(realAccountDeletes))

	log.Info("Keys in trie", "map", hashKeySet(keysInTrie))
	log.Info("Created keys", "map", hashKeySet(createdKeys))
	log.Info("Deleted keys", "map", hashKeySet(deletedKeys))
	log.Info("Always 0 keys", "map", hashKeySet(zeroGets))

	// t := ValidatorTrieFromObj(preObj)
	// ha := common.HexToHash("0xb4d14ec89c201c23aa60e231e3993b3966b33ff1f55d198ec25980957ab32065")
	// hk := common.HexToHash("0x0bd839f4461b871f3a9c86a40a5fdd92fd303f2683640e55dfb3105603a46223")
	//res := t.GetStateWithHashKey(ha.Bytes(), hk.Bytes())
	//log.Info("GetState result", "res", res)

	a := common.HexToHash("0xb4d14ec89c201c23aa60e231e3993b3966b33ff1f55d198ec25980957ab32065")
	k := common.HexToHash("0x299e3e924ceba6fe53dd5651a14c88eb9f6fb9e6c9763369a608e3310fe5709a")

	for key := range preObj.Keys {
		hk := common.BytesToHash(trie.PublicHashKey(key.Key().Bytes()))
		// ha := common.BytesToHash(trie.PublicHashKey(key.Addr().Bytes()))
		if hk.Cmp(k) == 0 {
			log.Info("Search Address", "hash", a, "addr", key.Addr())
			log.Info("Search Key", "hash", hk, "key", key.Key())
		}
	}

	// log.Info("Find all")
	// state.PublicFindAll(a, preObj.Journals)
	// state.PublicFindGetSets(a, k, preObj.Journals)
	//log.Info("Return")

	// eq := reflect.DeepEqual(accountsFound, accountsInTrie)
	// if eq {
	//	log.Info("Equal found and in journal")
	//	return true
	// } else {
	//	log.Error("Differing", "accountsFound", accountsFound, "accountsInTrie", accountsInTrie)
	//	return false
	//}
	return true
}

func validatePostLog(postObj *state.PostLog) bool {
	postAccounts, _ := ExploreTrie(postObj)
	postKeys, _ := ExploreTrieKeys(postObj)

	accountsFound := listToSet(postAccounts)
	// keysFound := listToSet(postKeys)

	log.Info("Post accounts", "mao", accountsFound)
	log.Info("Post keys", "map", postKeys)

	t := ValidatorTrieFromObj(postObj)
	ha := common.HexToHash("0xb4d14ec89c201c23aa60e231e3993b3966b33ff1f55d198ec25980957ab32065")
	hk := common.HexToHash("0x0bd839f4461b871f3a9c86a40a5fdd92fd303f2683640e55dfb3105603a46223")
	res := t.GetStateWithHashKey(ha.Bytes(), hk.Bytes())
	log.Info("GetState result", "res", res)

	return true
}

// Checks that the accounts reachable by traversing the saved hashes is the same
// as the set if reading from the journal of this block. It's good validation
// that the data collected is complete.
func validatePrePost(preObj *state.PreLog, postObj *state.PostLog) bool {

	// Go through the journal and determine which accounts already existed before this block
	// and check that the same accounts are found when the trie encoded by the node hashes is
	// traversed.
	// if ignoreJournal(preObj.Journals) {
	if ignorePrePost(preObj, postObj) {
		// log.Info("An empty journal is valid.")
		return true
	}

	preKeys, ok := ExploreTrie(preObj)
	_, exists := postObj.AccountNodes[preObj.Root]
	log.Info("Does root exist in post?", "exists", exists)

	if !ok {
		// check whether the root is in the postLog
		panic("")
	}

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
	postKeys, _ := ExploreTrie(postObj)
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
