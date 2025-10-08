package main

import (
	"os"
	"fmt"
	_"math/big"
	"reflect"
	"maps"
	"strings"
	"strconv"
	"sort"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/state"
	_ "github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/trie"
)

func CheckPostDataLogsEverything(dir string) {
	logFiles := getLogFilesSorted(dir)
	log.Info("Number of logs", "n", len(logFiles))


	//for _, obj := range logFiles[0] {
	for j := 0; j < len(logFiles) ; j++ {
		if j > 100 {
			break
		}
		for i := 0; i < len(logFiles[j]) - 1; i += 2 {

			pre := logFiles[j][i]
			post := logFiles[j][i+1]
			if pre.Type == PRE && post.Type == POST {
				preObj, exists := getPreObj(pre.Blockno, pre.Count)
				if !exists {
					log.Error("FIrst prelog should exists")
					break
				}
				log.Debug("Num journals", "l", len(preObj.Journals))
				postObj, exists := getPostObj(post.Blockno, post.Count)
				if !exists {
					log.Error("Post obj should never not exist, only preobj shouldn't exist", "block", post.Blockno, "count", post.Count)
					panic("Read postlog error")
				}

				if ignoreJournal(preObj.Journals) {
					log.Info("An empty journal is valid.")
					//return true, nil, nil, nil
					continue
				}
				
				_, ok := ExploreTrie(preObj)

				if !ok {
					_, exists := postObj.AccountNodes[preObj.Root]
					if !exists {
						panic("Root isn't in postlog either")
					} else {
						log.Debug("Dont with this block preLog is empty")
					}
					continue
				}

				success := validatePreLog(preObj, postObj)
				if !success {
					break
				}
				//
				//validatePostLog(postObj, preObj, accounts, deletes, accountsFound)
			}  else {
				panic(fmt.Sprintf("weird logfiles: %v", logFiles[0]))
			}
			//else if obj.Type == POST {
			//}
		}
	}

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

	// validation test for JournalToExport
	ejournals := state.JournalsToExported(preObj.Journals)
	eCreatedAccounts := GetCreatedAccountsExported(ejournals)
	eDeletedAccounts := GetDeletedAccountsExported(ejournals)
	eEmptyDeletes := GetEmptyDeletesExported(preObj.EmptyDeletes, ejournals)

	anyProblem := false
	if !maps.Equal(createdAccounts, eCreatedAccounts) {
		log.Error("create accounts not the same", "createdAccounts", len(createdAccounts), "eCreatedAccounts", len(eCreatedAccounts))
		anyProblem = true
	}

	if !maps.Equal(deletedAccounts, eDeletedAccounts) {
		log.Error("create accounts not the same", "deletedAccounts", len(deletedAccounts), "eDeletedAccounts", len(eDeletedAccounts))
		anyProblem = true
	}

	if !maps.Equal(emptyDeletes, eEmptyDeletes) {
		log.Error("create accounts not the same", "emptyDeletes", len(emptyDeletes), "eEmptyDeletes", len(eEmptyDeletes))
		anyProblem = true
	}

	if anyProblem {
		panic("Validation failed")
	}
		

	return mapSubtract(createdAccounts, emptyDeletes), MergeMaps(deletedAccounts, emptyDeletes), emptyDeletes
}

func validatePreLog(preObj *state.PreLog, postObj *state.PostLog) bool {
	// check that the trie finds all the accounts in the trie
	// get all accounts found by the trie (hashed keys)
	if ignoreJournal(preObj.Journals) {
		log.Info("An empty journal is valid.")
		return true
	}

	
	// IMPORTANT: there are duplicate node hashes in the tries of different
	// tries and that makes sense if the key is 1 and the value is 1
	// accountHashes, _ := ExploreTrieAllHashes(preObj)
	// c := findDuplicateHashes(accountHashes)
	// if c > 0 {
	// 	panic("c>0")
	// }

	preAccounts, _ := ExploreTrie(preObj)
	//preTrie := ValidatorTrieFromObj(preObj)
	hPreAccountsReached := listToSet(preAccounts)
	ejournals := state.JournalsToExported(preObj.Journals)

	// all the accounts that were created in this set and persist to the
	// future, all other created and deleted will not be returned here
	// some created accounts may be deleted because of being empty
	// and that won't be captured by reverts or self destructs
	createdAccounts, deletedAccounts, emptyDeletes := checkCreatesDeletes(preObj)
	hPreDeletedAccounts := hashAddressSet(deletedAccounts)
	hPreCreatedAccounts := hashAddressSet(createdAccounts)
	_ = hPreCreatedAccounts
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

	eq := reflect.DeepEqual(hPreAccountsReached, hExistingAccounts)
	if eq {
		log.Info("Equal found and in journal")
	} else {
		//log.Error("Differing", "hPreAccountsReached", hPreAccountsReached, "hExistingAccounts", hExistingAccounts)
		log.Error("Found - in trie", "m", len(mapSubtract(hPreAccountsReached, hExistingAccounts)))
		log.Error("in trie - Found", "m", len(mapSubtract(hExistingAccounts, hPreAccountsReached)))
	}

	hKeysInObj, hKeysInObjPreimages := hashKeySet(mapToSet(preObj.Keys))
	_, _ = hKeysInObj, hKeysInObjPreimages
	createdKeys := state.GetCreatedKeys(preObj.Journals)
	eCreatedKeys := GetCreatedKeysExported(ejournals)

	hCreatedKeys, hCreatedKeysPreimages := hashKeySet(createdKeys)
	_, _ = hCreatedKeys, hCreatedKeysPreimages

	zeroGets := state.GetKeysAlwaysZero(preObj.Journals)
	eZeroGets := GetKeysAlwaysZeroExported(ejournals)
	hZeroGets, hZeroGetsPreimages := hashKeySet(zeroGets)
	_, _ = hZeroGets, hZeroGetsPreimages

	anyFail := false
	if !maps.Equal(eCreatedKeys, createdKeys) {
		log.Error("Keys not equal", "createdKeys", len(createdKeys), "eCreatedKeys", len(eCreatedKeys))
		anyFail = true
	}

	if !maps.Equal(eZeroGets, zeroGets) {
		log.Error("Keys not equal", "zeroGets", len(zeroGets), "eZeroGets", len(eZeroGets))
		anyFail = true
	}
	
	if anyFail {
		panic("Validatioojn fail")
	}


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
			// this is the onyl thing we care about because this means there are journals accesses that
			// the data doesn't account for 

			// get the preimages and list which ones aren't in the other
			for ha := range intrie_found {
				a, ok := preimageMap[ha.HashAddr()]
				if ok {
					different[a] = true
				}
			}
			log.Debug("In journal but not in found", "addrs", different)
			panic("")
		} 
	}

	postAccounts, _ := ExploreTrie(postObj)
	hPostAccountsReached := listToSet(postAccounts)
	preFinalAccounts := mapSubtract(mapAdd(mapToSet(preObj.Accounts), createdAccounts), deletedAccounts)
	hPreFinalAccounts := hashAddressSet(preFinalAccounts)
	hExpectedTrieAccounts := mapSubtract(mapAdd(hPreAccountsReached, hPreCreatedAccounts), hPreDeletedAccounts)
	_, _ = hPostAccountsReached, hExpectedTrieAccounts

	postFound_preTrie := mapSubtract(hPostAccountsReached, hExpectedTrieAccounts)
	preTrie_postFound := mapSubtract(hExpectedTrieAccounts, hPostAccountsReached)

	// compare tries
	log.Debug("post found", "m", len(hPostAccountsReached))
	log.Debug("from pre trie", "m", len(hExpectedTrieAccounts))
	log.Debug("post found - from pre trie", "m", len(postFound_preTrie))
	log.Debug("from pre trie - post found", "m", len(preTrie_postFound))

	// compare post trie to inferred from journal
	postFound_preJournal := mapSubtract(hPostAccountsReached, hPreFinalAccounts)
	preJournal_postFound := mapSubtract(hPreFinalAccounts, hPostAccountsReached)
	log.Debug("from pre journal", "m", len(hPreFinalAccounts))
	log.Debug("post found - pre journal", "m", len(postFound_preJournal))
	log.Debug("pre journal - post found", "m", len(preJournal_postFound))
	if len(postFound_preJournal) != 0 {
		panic("postFound_preJourna")
	} 
	if len(preJournal_postFound) != 0 {
		panic("preJournal_postFound")
	}


	return true
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

func validatePostLogAccounts(postObj *state.PostLog, preObj *state.PreLog, createdAccounts map[common.Address]bool, preDeleted map[common.Address]bool, preFound map[common.Hash]bool) bool {
	postAccounts, _ := ExploreTrie(postObj)
	preAccounts, _ := ExploreTrie(preObj)
	hPreAccountsReached := listToSet(preAccounts)
	hPreCreatedAccounts := hashAddressSet(createdAccounts)
	hPreDeletedAccounts := hashAddressSet(preDeleted)
	hAccountsReached := listToSet(postAccounts)
	//postKeys, _ := ExploreTrieKeys(postObj)

	preFinalAccounts := mapSubtract(mapAdd(mapToSet(preObj.Accounts), createdAccounts), preDeleted)
	//preFinalAccounts := mapAdd(mapToSet(preObj.Accounts), createdAccounts)
	//preFinalAccounts := mapToSet(preObj.Accounts)
	hPreFinalAccounts := hashAddressSet(preFinalAccounts)
	_ = hPreFinalAccounts
	hExpectedTrieAccounts := mapSubtract(mapAdd(hPreAccountsReached, hPreCreatedAccounts), hPreDeletedAccounts)

	postFound_preTrie := mapSubtract(hAccountsReached, hExpectedTrieAccounts)
	preTrie_postFound := mapSubtract(hExpectedTrieAccounts, hAccountsReached)


	// compare tries
	log.Debug("post found", "m", len(hAccountsReached))
	log.Debug("from pre trie", "m", len(hExpectedTrieAccounts))
	log.Debug("post found - from pre trie", "m", len(postFound_preTrie))
	log.Debug("from pre trie - post found", "m", len(preTrie_postFound))

	// compare post trie to inferred from journal
	postFound_preJournal := mapSubtract(hAccountsReached, hPreFinalAccounts)
	preJournal_postFound := mapSubtract(hPreFinalAccounts, hAccountsReached)
	log.Debug("from pre journal", "m", len(hPreFinalAccounts))
	log.Debug("post found - pre journal", "m", len(postFound_preJournal))
	log.Debug("pre journal - post found", "m", len(preJournal_postFound))
	if len(postFound_preJournal) != 0 {
		panic("postFound_preJourna")
	} 
	if len(preJournal_postFound) != 0 {
		panic("preJournal_postFound")
	}

	//


	return true
}


func validatePostLog(postObj *state.PostLog, preObj *state.PreLog, createdAccounts map[common.Address]bool, preDeleted map[common.Address]bool, preFound map[common.Hash]bool) bool {
	validatePostLogAccounts(postObj, preObj, createdAccounts, preDeleted, preFound)
	//accountsFound := listToSet(postAccounts)
	// keysFound := listToSet(postKeys)

	//log.Info("Post keys", "map", postKeys)

	//t := ValidatorTrieFromObj(postObj)
	//ha := common.HexToHash("0xb4d14ec89c201c23aa60e231e3993b3966b33ff1f55d198ec25980957ab32065")
	//hk := common.HexToHash("0x0bd839f4461b871f3a9c86a40a5fdd92fd303f2683640e55dfb3105603a46223")
	//res := t.GetStateWithHashKey(ha.Bytes(), hk.Bytes())
	//log.Info("GetState result", "res", res)

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

func findDuplicateHashes(m map[common.Hash]map[common.Hash][]byte) int {
	hashes := make(map[common.Hash][]byte)
	count := 0
	for _, hns := range m {
		for hn := range hns {
			// store the preimages
			oldraw, ok := hashes[hn]
			if ok {
				log.Error("Duplicate node hash", "hn", hn)
				newraw, _ := hns[hn]
				// decode the nodes
				oldn, err := trie.PublicDecodeNode(nil, oldraw)
				if err != nil {
					log.Error("Failed to decode old node", "oldn", oldraw)
				} 

				newn, err := trie.PublicDecodeNode(nil, newraw)
				if err != nil {
					log.Error("Failed to decode new node", "newn", newraw)
				}

				log.Error("The nodes", "oldn", oldn, "newn", newn)
				count++
			} else {
				hashes[hn] = hns[hn]
			}
		}
	}
	return count
}


// Check the logs of a specific block (basically check how many there are and which ones)
func investigateBlock(dir string, blockno int) {
	var logFiles []LogFile
	files, err := os.ReadDir(dir)
	if err != nil {
		panic(fmt.Sprintf("Error reading dir %v", err))
	}
	for _, file := range files {
		if file.IsDir() {
			continue
		}

		filename := file.Name()
		// Check if the filename matches the format "string-number-number.json"
		if strings.HasSuffix(filename, ".json") {
			parts := strings.Split(strings.TrimSuffix(filename, ".json"), "-")
			if len(parts) == 3 {
				var preorpost Prepost
				if parts[0] == "predata" {
					preorpost = PRE
				} else if parts[0] == "postdata" {
					preorpost = POST
				} else {
					panic(fmt.Sprintf("file is neither predata or postdata : %v", parts[0]))
				}

				blockno, err := strconv.Atoi(parts[1])
				if err != nil {
					panic(fmt.Sprintf("Blockno couldn't be read as an int: %v", parts[1]))
				}
				iteration, err := strconv.Atoi(parts[2])
				if err != nil {
					panic(fmt.Sprintf("Iteration couldn't be read as an int: %v", parts[2]))
				}
		
				if blockno == 359791727 {
					lf := LogFile{
						FileName: filename,
						Blockno: blockno,
						Type: preorpost,
						Count: iteration,
					}
					logFiles = append(logFiles, lf)
				}
			}
		}
	}
	sort.Sort(ByBlock(logFiles))

	// group them by block number in a 2d array
	var groupedLogFiles [][]LogFile
	currBlockno := 0
		
	for _, lf := range logFiles {
		if lf.Blockno != currBlockno {
			groupedLogFiles = append(groupedLogFiles, []LogFile{})
			currBlockno = lf.Blockno
		}
		groupedLogFiles[len(groupedLogFiles)-1] = append(groupedLogFiles[len(groupedLogFiles)-1], lf)
	}

	if len(groupedLogFiles) != 1 {
		panic("Too many log files")
	}
	
	targetLogFiles := groupedLogFiles[0]
	sort.Sort(ByTotalOrder(targetLogFiles))
	log.Info("target log files", "sorted", targetLogFiles)	
}

