package main 

import (
    "slices"
    "github.com/ethereum/go-ethereum/core/state"
    "github.com/ethereum/go-ethereum/common"
    "github.com/ethereum/go-ethereum/log"
    "github.com/ethereum/go-ethereum/trie"
)

type AccessType int

// all accesses are of the form 'create', 'deleted', 'get', 'update'
const (
	GET AccessType = iota
	UPDATE
	CREATE
	DELETE
)

type Access struct {
	kind	AccessType
}

type Node struct {
	Addr common.Hash
	NodeHash  common.Hash
}

// for the preLog we don't really care about them in order, we just want
// a set of all accesses so we can figure out hits and misses in the cache
func AccessesForValidation(preObj *state.PreLog) map[Node]bool {
    out := make(map[Node]bool)
    ejournals := state.JournalsToExported(preObj.Journals)
    //vtrie := ValidatorTrieFromObj(preObj)

    for _, journal := range ejournals {
        for _, e := range journal {
            switch logEntry := (e.Entry).(type) {
            // In both CreateObject and CreateContract we don't need to do
            // anything special because only Get requests will log everything
            case state.GetStateObjectEntry:
                // In GetStateObjectEntry, the path is already stored in the data
                // of the preObj, we just need to turn it into an (haddr, hkey) pair
                addr := logEntry.Account
                pathHashes, exists := preObj.Accounts[addr]
                if !exists {
                    // There is never a real data trie that is empty so always a path,
                    // and we should see accounts with no data
                    log.Error("getStateObjectEntry doesn't exist", "addr", addr)
                    panic("")
                }
                for _, h := range pathHashes {
                    n := Node{common.Hash{}, h}
                    out[n] = true
                }
            case state.GetStorageEntry:
                // For GetStorageEntry the Addr of the Node should be the hash
                // of the address so that we have unique nodes for different storage tries
                addr, key := logEntry.Account, logEntry.Key 
                kk := state.NewKeyKey(addr, key)
                pathHashes, exists := preObj.Keys[kk]
                if !exists {
                    log.Error("getStorageEntry doesn't exist", "key", kk)
                    panic("")
                }
                haddr := common.BytesToHash(trie.PublicHashKey(addr.Bytes()))
                for _, h := range pathHashes {
                    n := Node{haddr, h}
                    out[n] = true
                }
            case state.StorageChange:
                // nothing to be done for a storageChange, because the SetState
                // function always does a getStateObject first and then a getState
            }
        }
    }
    return out
}

func copyReverse[T any](l []T) []T {
    ret := make([]T, len(l))
    copy(ret, l)
    slices.Reverse(ret)
    return ret
}

// IMPORTANT: for now we push the create object paths on the first create in the block
// rather than at the last create that actually makes the create, this is slightly out of 
// order but it's not THAT big a deal for now

// IMPORTANT: another caveat here is that if there was a get request to an account
// in the preLog that didn't exist then a path was returned that possible contained 
// another leaf that was reached in search of the non-existent account. If the object
// was created, then the get request will not see that leaf we got to before (for validation)
// and we don't actually push it into the cache becuase we don't reach it in the trie.
// This also means that this caching isn't perfect as it should be but THINK ABOUT IT LATER.
// IFFF we push all the preLog stuff into the cache as well, then we'll capture all of that
func OrderedAccessesForPostLog(preObj *state.PreLog, postObj *state.PostLog) []Node {
    out := []Node{}
    ejournals := state.JournalsToExported(preObj.Journals)
    vtrie := ValidatorTrieFromObj(postObj)
    //created := GetCreatedAccountsExported(ejournals)
    created, _, _ := checkCreatesDeletes(preObj)

    createsAdded := make(map[common.Address]bool)
    //keysAdded := map[state.KeyKey]bool

    for _, journal := range ejournals {
        for _, e := range journal {
            switch logEntry := (e.Entry).(type) {
            case state.CreateObjectChange:
                // Only get it again if this create exists in the trie, otherwise
                // we don't care about it in the postLog, whatever had to be logged
                // was logged in the preLog
                addr := logEntry.Account
                v, _ := vtrie.GetWithPath(addr.Bytes())
                if v == nil {
                    // if this doesn't exist, it shouldn't also be in "created"
                    _, ok := created[addr]
                    if ok {
                        log.Error("Didn't find a created account in the post Trie", "addr", addr)
                        panic("")
                    }
                } else {
                    // if it exists in this trie, then it must have been created according
                    // to the journals
                    if _, ok := createsAdded[addr]; ok {
                        continue
                    }
                    
                    // log this new create account that exists
                    pathHashes, exists := postObj.Accounts[addr]
                    if !exists {
                        panic("Doesn't exist")
                    }
                    // NOTE: we don't need to reverse the order of pathHashes, because
                    // getLogged in the trie already returns the acces list in root->leaf
                    // order
                    for _, h := range pathHashes {
                        n := Node{common.Hash{}, h}
                        out = append(out, n)
                    }
                    createsAdded[addr] = true
                }
            case state.CreateContractChange:
                // nothig to do here really, anything useful is captured by either a 
                // get state object or a create object
            case state.GetStateObjectEntry:
                // we always want to log this because we want the nodes that were touched since
                // they might have changed
                addr := logEntry.Account
                pathHashes, exists := postObj.Accounts[addr]
                if !exists {
                    log.Error("State object should always be in accounts")
                    panic("")
                }
                // if this is a get to a newly created account, then in the preLog this was
                // just a single entry but now we're going to get the whole new path that was
                // created for it
                for _, h := range pathHashes {
                    n := Node{common.Hash{}, h}
                    out = append(out, n)
                }
            case state.GetStorageEntry:
                // the same thing for storage entries just log it regardless
                addr := logEntry.Account
                haddr := common.BytesToHash(trie.PublicHashKey(addr.Bytes()))
                key := logEntry.Key
                kk := state.NewKeyKey(addr, key)
                pathHashes, exists := postObj.Keys[kk]
                if !exists {
                    log.Error("Should definitely exist")
                    panic("")
                }

                for _, h := range pathHashes {
                    // hash the address first
                    n := Node{haddr, h}
                    out = append(out, n)
                }
            }
        }
    }

    return out
}
