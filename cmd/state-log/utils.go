package main

import (
	_"fmt"
	"reflect"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/trie"
)

type Address = common.Address
type KK = state.KeyKey
type HK = state.HashedKeyKey


// Map and Set operations
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

func listToMap[K comparable](l []K) map[K]bool {
	out := make(map[K]bool)
	for _, e := range l {
		out[e] = true
	}
	return out
}

func setToList[K comparable](m map[K]bool) []K {
	out := make([]K, len(m))
	i := 0
	for k := range m {
		out[i] = k
		i++
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

func mapAdd[K comparable, V any](m map[K]V, add map[K]V) map[K]V {
	out := make(map[K]V)
	for k := range m {
		out[k] = m[k]
	}
	for k := range add {
		out[k] = add[k]
	}
	return out
}

func mapSubtract[K comparable, V comparable](m map[K]V, subtract map[K]V) map[K]V {
	out := make(map[K]V)
	for k := range m {
		_, ok := subtract[k]
		if !ok {
			out[k] = m[k]
		} else {
			mv := m[k]
			subv := subtract[k]
			if subv != mv {
				panic("Keys don't have the same valuie")
			}
		}
	}
	return out
}

func arbMapElement[K comparable, V any](m map[K]V) (K, V) {
	var zeroK K
	var zeroV V
	for k, v := range m {
		return k, v
	}
	return zeroK, zeroV
}


// Hashing addresses and keys utils

func hashAddressSet(m map[common.Address]bool) map[common.Hash]bool {
	out := make(map[common.Hash]bool)
	for addr := range m {
		out[common.BytesToHash(trie.PublicHashKey(addr.Bytes()))] = m[addr]
	}
	return out
}

// find the preimage of a hash from a set of addresses (might not exist)
func findAddressPreimage[V any](target common.Hash, m map[common.Address]V) common.Address {
	for addr := range m {
		ha := common.BytesToHash(trie.PublicHashKey(addr.Bytes()))
		if target.Cmp(ha) == 0 {
			return addr	
		}
	}
	return common.Address{}
}

// hash a set of KeyKeys into a set of HashedKeyKeys
// and returns a set of preimages from HKK -> KK
func hashKeySet(m map[KK]bool) (map[HK]bool, map[HK]KK) {
	hashes := make(map[HK]bool)
	preimages := make(map[HK]KK)

	for kk := range m {
		ha := common.BytesToHash(trie.PublicHashKey(kk.Addr().Bytes()))
		hk := common.BytesToHash(trie.PublicHashKey(kk.Key().Bytes()))
		hkk := state.NewHashedKeyKey(ha, hk)
		hashes[hkk] = true
		preimages[hkk] = kk
	}
	return hashes, preimages
}

// create two maps given a set of preimges (KeyKeys) and hashes (HashedKeyKeys)
// first map is hash -> preimage second is preimage -> hash
func hkkPreimages[V1 any, V2 any](preimages map[KK]V1, hashes map[HK]V2) (map[common.Hash]common.Address, map[common.Address]common.Hash) {
	res := make(map[common.Hash]common.Address)
	resH := make(map[common.Address]common.Hash)
	for preimage := range preimages {
		h := common.BytesToHash(trie.PublicHashKey(preimage.Addr().Bytes()))
		hk := state.NewHashedKeyKey(h, preimage.Key())
		_, ok := hashes[hk]
		if ok {
			res[h] = preimage.Addr()
			resH[preimage.Addr()] = h
		}
	}
	return res, resH
}

// Searching sets for addresses and keys

// return the set of keys for a specific address in a set of KeyKeys
func keysForAddr(target common.Address, keys map[KK]bool) map[common.Hash]bool {
	res := make(map[common.Hash]bool)
	for kk := range keys {
		if kk.Addr().Cmp(target) == 0 {
			res[kk.Key()] = true
		}
	}
	return res
}

// return the list of HashedKeyKeys of a specific Hash(address) from a set m
func countHKKInSet(target common.Hash, m map[state.HashedKeyKey]bool) []state.HashedKeyKey {
	c := []state.HashedKeyKey{}
	for k := range m {
		if target.Cmp(k.HashAddr()) == 0 {
			c = append(c, k)
		}
	}
	return c
}

// return just the hashed keys from a set of HashedKeyKeys for a specific target
// hash address
func keysForHashAddr(target common.Hash, hashKeys map[HK]bool) map[common.Hash]bool {
	res := make(map[common.Hash]bool)
	for hk := range hashKeys {
		if hk.HashAddr().Cmp(target) == 0 {
			res[hk.Key()] = true
		}
	}
	return res
}


// utils on logs

// are these two prelog objects identical (same Accounts, AccountNodes, Keys, and KeyNodes)
func IsIdenticalPre(obj1 *state.PreLog, obj2 *state.PreLog) bool {
	log.Info("Identical check", "root1", obj1.Root, "root2", obj2.Root)
	if !reflect.DeepEqual(obj1.Accounts, obj2.Accounts) {
		log.Error("Accounts differ")
		return false
	}

	if !reflect.DeepEqual(obj1.AccountNodes, obj2.AccountNodes) {
		log.Error("AccountNodes differ")
		return false
	}

	if !reflect.DeepEqual(obj1.Keys, obj2.Keys) {
		log.Error("Keys differ")
		return false
	}

	if !reflect.DeepEqual(obj1.KeyNodes, obj2.KeyNodes) {
		log.Error("KeyNodes differ")
		return false
	}

	return true
}


// journal operations

// the real key here is that something might be deletd because it's empty in
// one block and then is created again in the next block. We need to make sure
// that things that eventually end up existing aren't returned in this map.
func GetEmptys(preObj *state.PreLog) map[common.Address]bool {
	// there should always be as many journals as there are empty slices
	created := state.GetEmptyDeletes(preObj.EmptyDeletes, preObj.Journals)

	return created
}

// if all the journals in this slice are len zero then ignore it (true)
func ignoreJournal(j [][]state.LogJournalEntry) bool {
	for _, jn := range j {
		if len(jn) > 0 {
			return false
		}
	}
	return true
}

// here we want to check whether the preLog hash the root in it
// if it doesn't then we can skip this preLog and this whole pre/post set
func ignorePrePost(preObj *state.PreLog, postObj *state.PostLog) bool {
	_, ok := preObj.AccountNodes[preObj.Root]
	if !ok {
		log.Info("Root doesn't exist, so there were no new activity in this pre log.")
		// in this case we should assert that the postLog has this same root or else there's something missing
		// if the postLog root is different then something happened in between that wasn't accounted for
		_, ok = postObj.AccountNodes[preObj.Root]
		if ok {
			return true
		} else {
			log.Error("Prelog root isn't in postlog either.", "pre", preObj.Root, "por", postObj.Root)
			panic("")
		}
	}

	if ignoreJournal(preObj.Journals) {
		return true
	}

	return false
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

func samplePreData(preObj *state.PreLog) {
	if len(preObj.Journals) > 0 {
		log.Info("Read pre data", "root", preObj.Root, "data", preObj.Journals[0][0:min(4, len(preObj.Journals[0]))])
	} else {
		log.Info("Journal is empty")
	}
	log.Info("Maps", "accounts", len(preObj.Accounts), "accountNodes", len(preObj.AccountNodes), "keys", len(preObj.Keys), "keyNodes", len(preObj.KeyNodes))
	log.Info("Emptys", "list", preObj.EmptyDeletes)
}
