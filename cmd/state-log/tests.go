package main

import (
	"fmt"
	_"math/big"
	"reflect"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/state"
	_ "github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/trie"
)

func CheckPostDataLogsEverything(dir string) {
	logFiles := getLogFilesSorted(dir)
	log.Info("Number of logs", "n", len(logFiles))

	//blockno := big.NewInt(0)

	preObj, exists := getPreObj(logFiles[0][0].Blockno, 1)
	if !exists {
		log.Error("FIrst prelog should exists")
		panic("Read preloog error")
	}

	_, exists = getPostObj(logFiles[0][0].Blockno, 1)
	if !exists {
		log.Error("Last post log version 2 should be there")
		panic("Read post log error")
	}

	validatePreLog(preObj)
	//validatePostLog(postObj)

	//ExploreTrieKeys(preObj)
}

func checkCreatesDeletes(preObj *state.PreLog) (state.Set, state.Set, state.Set) {
	createdAccounts := state.GetCreatedAccounts(preObj.Journals)
	deletedAccounts := state.GetDeletedAccounts(preObj.Journals)
	emptyDeletes := state.GetEmptyDeletes(preObj.EmptyDeletes, preObj.Journals)
	// sanity check our data
	for _, l := range preObj.CreateDelete {
		for _, addr := range l {
			_, created := createdAccounts[addr]
			_, deleted := deletedAccounts[addr]
			if created || deleted {
				panic(fmt.Sprintf("Created (%v) or Deleted(%v) returned an account that was createdAndDeleted: %v", created, deleted, addr))
			}
		}
	}
	return mapSubtract(createdAccounts, emptyDeletes), MergeMaps(deletedAccounts, emptyDeletes), emptyDeletes
}

func validatePreLog(preObj *state.PreLog) bool {
	// check that the trie finds all the accounts in the trie
	// get all accounts found by the trie (hashed keys)
	if ignoreJournal(preObj.Journals) {
		log.Info("An empty journal is valid.")
		return true
	}

	preAccounts, _ := ExploreTrie(preObj)
	//preTrie := ValidatorTrieFromObj(preObj)
	hAccountsReached := listToSet(preAccounts)

	// all the accounts that were created in this set and persist to the
	// future, all other created and deleted will not be returned here
	// some created accounts may be deleted because of being empty
	// and that won't be captured by reverts or self destructs
	createdAccounts, _, emptyDeletes := checkCreatesDeletes(preObj)
	hCreatedAccounts := hashAddressSet(createdAccounts)
	_ = hCreatedAccounts
	hEmptyDeletes := hashAddressSet(emptyDeletes)
	_ = hEmptyDeletes

	// The accounts that should already be in the trie according to this journal.
	// Created accounts aren't in the trie yet, and neither are the accounts that were
	// created and deleted because they were empty. We expect to find exactly these
	// same accounts when creating a trie with the stored nodes.
	hAccountsInObj := hashAddressSet(mapToSet(preObj.Accounts))
	_ = hAccountsInObj
	existingAccounts := mapSubtract(mapSubtract(mapToSet(preObj.Accounts), createdAccounts), emptyDeletes)
	hExistingAccounts := hashAddressSet(existingAccounts)

	// t := ValidatorTrieFromObj(preObj)
	// ha := common.HexToHash("0xb4d14ec89c201c23aa60e231e3993b3966b33ff1f55d198ec25980957ab32065")
	// hk := common.HexToHash("0x0bd839f4461b871f3a9c86a40a5fdd92fd303f2683640e55dfb3105603a46223")
	//res := t.GetStateWithHashKey(ha.Bytes(), hk.Bytes())
	//log.Info("GetState result", "res", res)

	//a := common.HexToHash("0xb4d14ec89c201c23aa60e231e3993b3966b33ff1f55d198ec25980957ab32065")
	//k := common.HexToHash("0x299e3e924ceba6fe53dd5651a14c88eb9f6fb9e6c9763369a608e3310fe5709a")

	//for key := range preObj.Keys {
	//	hk := common.BytesToHash(trie.PublicHashKey(key.Key().Bytes()))
	//	// ha := common.BytesToHash(trie.PublicHashKey(key.Addr().Bytes()))
	//	if hk.Cmp(k) == 0 {
	//		log.Info("Search Address", "hash", a, "addr", key.Addr())
	//		log.Info("Search Key", "hash", hk, "key", key.Key())
	//	}
	//}

	// log.Info("Find all")
	// state.PublicFindAll(a, preObj.Journals)
	// state.PublicFindGetSets(a, k, preObj.Journals)
	//log.Info("Return")

	eq := reflect.DeepEqual(hAccountsReached, hExistingAccounts)
	if eq {
		log.Info("Equal found and in journal")
	} else {
		//log.Error("Differing", "hAccountsReached", hAccountsReached, "hExistingAccounts", hExistingAccounts)
		log.Error("Found - in trie", "m", mapSubtract(hAccountsReached, hExistingAccounts))
		log.Error("in trie - Found", "m", mapSubtract(hExistingAccounts, hAccountsReached))
	}

	hKeysInObj, hKeysInObjPreimages := hashKeySet(mapToSet(preObj.Keys))
	_, _ = hKeysInObj, hKeysInObjPreimages
	createdKeys := state.GetCreatedKeys(preObj.Journals)
	hCreatedKeys, hCreatedKeysPreimages := hashKeySet(createdKeys)
	_, _ = hCreatedKeys, hCreatedKeysPreimages
	zeroGets := state.GetKeysAlwaysZero(preObj.Journals)
	hZeroGets, hZeroGetsPreimages := hashKeySet(zeroGets)
	_, _ = hZeroGets, hZeroGetsPreimages
	//deletedKeys := state.GetDeletedKeys(preObj.Journals)
	keysInTrie := mapSubtract(mapToSet(preObj.Keys), createdKeys)
	keysInTrie = mapSubtract(keysInTrie, zeroGets)

	// KeyKey from the logs have an address and an unhashed key, but the
	// trie search will always return the hashed address and the hashed key.
	// Therefore we need to hash the keys from the log to be able to compare 
	// it to what is found by the trie.
	hashedKeysInTrie := make(map[state.HashedKeyKey]bool)
	keyPreimages := make(map[common.Hash]common.Hash)
	keyHashes := make(map[common.Hash]common.Hash)
	for k := range keysInTrie {
		ha := common.BytesToHash(trie.PublicHashKey(k.Addr().Bytes()))
		hk := common.BytesToHash(trie.PublicHashKey(k.Key().Bytes()))
		hkk := state.NewHashedKeyKey(ha, hk)
		hashedKeysInTrie[hkk] = keysInTrie[k]
		keyPreimages[hk] = k.Key()
		keyHashes[k.Key()] = hk
	}

	preKeys, _ := ExploreTrieKeys(preObj)
	// make this into a HashedKeyKey map as well
	hashedKeysFound := make(map[state.HashedKeyKey]bool)
	for ha, hks := range preKeys {
		for _, hk := range hks {
			hkk := state.NewHashedKeyKey(ha, hk)
			hashedKeysFound[hkk] = true
		}
	}

	keyEq := reflect.DeepEqual(hashedKeysFound, hashedKeysInTrie)
	if keyEq {
		log.Info("Keys are equal")
	} else {
		intrie_found := mapSubtract(hashedKeysInTrie, hashedKeysFound)
		found_intrie := mapSubtract(hashedKeysFound, hashedKeysInTrie)
		log.Error("keys not equal", "keysInTrie", len(hashedKeysInTrie), "keysFound", len(hashedKeysFound))
		log.Error("Difference", "inTrie - found", len(intrie_found), "found - in trie", len(found_intrie))

		// what addresses have the keys not in the other
		preimageMap, _ := hkkPreimages(keysInTrie, hashedKeysInTrie)
		// the addresses of the keys

		different := make(map[common.Address]bool)
		diffNoPreimage := make(map[common.Hash]bool)
		_ = diffNoPreimage
		if len(intrie_found) > 0 && len(found_intrie) == 0 {
			// get the preimages and list which ones aren't in the other
			for ha := range intrie_found {
				a, ok := preimageMap[ha.HashAddr()]
				if ok {
					different[a] = true
				}
			}
			log.Debug("In journal but not in found", "addrs", different)
		} 

///// The code below is for diagnosing the extra keys that are found in the trie, but 
///// aren't in the journal. We figured out that the extra keys present is a case of a
///// Get request in the journal to a key with a matching prefix that traversed all the 
///// way down the trie, to the short node{valueNode}, and returned nil but logged the 
///// leaf as well. If you print the zeroGets for the accounts and the keys not found in the
///// journal, you notice the missing keys all have a decent shared prefix with the zero gets.
		//else if len(found_intrie) > 0 && len(intrie_found) == 0 {
		//	for ha := range found_intrie {
		//		a, ok := preimageMap[ha.HashAddr()]
		//		if ok {
		//			different[a] = true
		//		} else {
		//			diffNoPreimage[ha.HashAddr()] = true
		//		}
		//	}
		//	log.Debug("found but not in journal", "addrs", different, "no preimage", len(diffNoPreimage))
		//	for hd := range diffNoPreimage {
		//		c := state.PublicFindAllHashKeyCount(hd, preObj.Journals)
		//		log.Debug("no preimage", "addr", hd, "count", c)
		//	}

		//	targetha := common.HexToHash("0xb4d14ec89c201c23aa60e231e3993b3966b33ff1f55d198ec25980957ab32065")
		//	targeta := common.HexToAddress("0xA4b05FffffFffFFFFfFFfffFfffFFfffFfFfFFFf")

		//	// the keys of this found in journal and only in trie
		//	cInJournal := countHKKInSet(targetha, hashedKeysInTrie)
		//	cInTrie := countHKKInSet(targetha, found_intrie)
		//	cZeroGets := countHKKInSet(targetha, hZeroGets)

		//	log.Debug("Target address", "addr", targeta, "cInJournal", len(cInJournal), "cInTrie", len(cInTrie), "zeroGets", len(cZeroGets))

		//	log.Debug("cInJournal")
		//	for _, inj := range cInJournal {
		//		log.Debug("Hashed key", "hk", inj)
		//		state.PublicFindAllHashKeyKey(inj, preObj.Journals)
		//	}
		//	log.Debug("found_intrie")
		//	for _, inj := range cInTrie {
		//		log.Debug("Hashed key", "hk", inj)
		//		state.PublicFindAllHashKeyKey(inj, preObj.Journals)
		//	}

		//	for _, inj := range cZeroGets {
		//		log.Debug("Zero get", "hk", inj)
		//	}


		//	_, hkInObj := hKeysInObj[targethkk]
		//	_, hkInCreated := hKeysInObj[targethkk]
		//	log.Debug("Target membership", "inObj", hkInObj, "inCreated", hkInCreated)
		//	state.PublicFindAllHashKey(targethkk.HashAddr(), preObj.Journals)

		//	 inspect one element of the nopreimage set
		//	k, _ := arbMapElement(found_intrie)
		//	log.Debug("Arb element", "k", k)
		//	state.PublicFindAllHashKeyKey(k, preObj.Journals)
		//	log.Debug("Account actions", "ha", k.HashAddr())
		//	state.PublicFindAllHashKeyStorage(k.HashAddr(), preObj.Journals)

		//	//for d := range different {
		//	//	log.Debug("Difference", "addr", d, 
		//	//	state.PublicFindAll(d, preObj.Journals)
		//	//}
		//} else {
		//	panic(fmt.Sprintf("Both have exclusive elements"))
		//}
/////
	}

	return true
}

func arbMapElement[K comparable, V any](m map[K]V) (K, V) {
	var zeroK K
	var zeroV V
	for k, v := range m {
		return k, v
	}
	return zeroK, zeroV
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
