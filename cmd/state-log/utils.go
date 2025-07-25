package main

import (
	"fmt"
	"reflect"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/trie"
)

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

func hashAddressSet(m map[common.Address]bool) map[common.Hash]bool {
	out := make(map[common.Hash]bool)
	for addr := range m {
		out[common.BytesToHash(trie.PublicHashKey(addr.Bytes()))] = m[addr]
		log.Info("Preimage", "addr", addr, "hash", common.BytesToHash(trie.PublicHashKey(addr.Bytes())))
	}
	return out
}

type HashedKeyKey struct {
	addr common.Hash
	key  common.Hash
}

func (k HashedKeyKey) Format(s fmt.State, c rune) {
	k.addr.Format(s, c)
	s.Write([]byte(", "))
	k.key.Format(s, c)
}

func hashKeySet(m map[state.KeyKey]bool) map[HashedKeyKey]bool {
	out := make(map[HashedKeyKey]bool)
	for key := range m {
		ha := common.BytesToHash(trie.PublicHashKey(key.Addr().Bytes()))
		hk := common.BytesToHash(trie.PublicHashKey(key.Key().Bytes()))
		// out[common.BytesToHash(trie.PublicHashKey(key.Key().Bytes()))] = m[key]
		out[HashedKeyKey{ha, hk}] = m[key]
	}
	return out
}

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

// the real key here is that something might be deletd because it's empty in
// one block and then is created again in the next block. We need to make sure
// that things that eventually end up existing aren't returned in this map.
func GetEmptys(preObj *state.PreLog) map[common.Address]bool {
	// there should always be as many journals as there are empty slices
	created := state.GetEmptyDeletes(preObj.EmptyDeletes, preObj.Journals)

	return created
}

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
