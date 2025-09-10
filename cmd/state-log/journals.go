package main

import (
	"fmt"
	_"math/big"
	_"reflect"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/state"
	_ "github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/log"
	_"github.com/ethereum/go-ethereum/trie"
)

// Determine which accounts were created in this transaction. We 
// need to be careful to check for create changes that were reverted.
func GetCreatedAccountsExported(j [][]state.ExportedJournalEntry) state.Set {
	accountsCreated := make(state.Set)
	for _, jn := range j {
		for _, e := range jn {
			switch entry := (e.Entry).(type) {
			case state.CreateObjectChange:
				// A create object change should be added to the map 
				// only if this entry wasn't reverted. 
				if e.Reverted {
					continue
				}
				// check that it wasn't created previously, that's anomalous
				_, ok := accountsCreated[entry.Account]
				if ok {
					log.Error("Two un-reverted createObject changes to the same account", "addr", entry.Account)
					panic("err")
				}
				accountsCreated[entry.Account] = true
			case state.SelfDestructChange:
				// it is important to only look at the selfDestructs that have a corresponding
				// createObjectChange, becaused we only care about created accounts
				// if the selfDestruct was reverted, then whereever the original
				// create change is, whether itself reverted or now, we leave it
				// alone.
				if e.Reverted {
					continue
				}

				_, createdInThisJournal := accountsCreated[entry.Account]

				if createdInThisJournal {
					// just remove it from the accountsCreatedSet if it's there
					delete(accountsCreated, entry.Account)
					continue
				} 
				// if it wasn't created in this set of journals then we don't really care
			default: continue
			}
		}

	}
	return accountsCreated
}

// Gets only the accounts that existed before this set of journals (i.e.
// are in the trie). Ignore the ones created here and deleted here because
// those don't change the trie.
func GetDeletedAccountsExported(j [][]state.ExportedJournalEntry) state.Set {
	// need the set of created accounts to filter them out of the 
	// accounts the function returns
	createdAccounts := GetCreatedAccountsExported(j)
	deletedAccounts := make(state.Set)
	// We don't care about the selfDestructs
	// that occur because they aren't deletions due to being empty
	for _, jn := range j {
		for _, e := range jn {
			switch entry := (e.Entry).(type) {
			case state.SelfDestructChange:
				// We only care about this selfDestruct if it wasn't reverted
				// and it was for an account NOT created in this set of 
				// journals.
				_, wasCreated := createdAccounts[entry.Account]
				_, alreadyDeleted := deletedAccounts[entry.Account]
				if !wasCreated && !e.Reverted {
					if alreadyDeleted {
						panic(fmt.Sprintf("Two deletes to this same account: %v", entry.Account))
					}
					deletedAccounts[entry.Account] = true
				}					
			default:
			}
		}
	}
	return deletedAccounts
}

// The emptys list holds all the accounts that were empty at the end of the corresponding 
// journal. This function should go through that list and filter out the ones that are 
// created again in the future and eventually commited into the trie. The function returns
// the real set of accounts deleted because they were empty and no longer exist.
// IMPORTANT: we need to make sure that this function only deals with empty deletes
// and nothing else or we might end up double counting things that are in the other
// maps of the log like createdAndDeleted or real deletes/creates
func GetEmptyDeletesExported(emptys [][]common.Address, l [][]state.ExportedJournalEntry) state.Set {
	if len(emptys) != len(l) {
		panic(fmt.Sprintf("Unequal number of journals. emtpys=%v, journal=%v", len(emptys), len(l)))
	}

	// the real empty set will be used by "empty" lists
	// that need to check whether this was empty deleted in a perviou
	// "empty" list
	realEmptys := make(state.Set)
	
	for i := 0; i < len(emptys); i++ {
		// use a temporary map because we want realEmptys to only be
		// the empty deletes in previous lists so we can search and delete
		// them if we see a createObjectChange in this list 
		emptyDeletesThisRound := make(state.Set)
		// We have to go in lock step with the corresponding journal
		// for each "empty" list. First get all the empties in this
		// list, then go through the journal. If we see a createObjectChange
		// for a 
		for _, addr := range emptys[i] {
			_, ok := emptyDeletesThisRound[addr]
			if ok {
				// should be seeing this twice!!
				panic(fmt.Sprintf("Two empty deletes in the same list: %v", addr))
			}
			// since emptys are processed at the END of the logging, 
			// they can only be invalidated by future "empty" lists
			emptyDeletesThisRound[addr] = true
		}

		// now go through the journal and see if there are any in realEmptys
		// that need to be deleted. We don't care about the selfDestructs
		// that occur because they aren't deletions due to being empty
		for _, e := range l[i] {
			switch entry := (e.Entry).(type) {
			case state.CreateObjectChange:
				// if this is a create for something empty in this round then ignore it
				if _, thisRound := emptyDeletesThisRound[entry.Account]; thisRound {
					continue
				}
				// if this account was empty deleted in a previous iteration (i.e.
				// it is in realEmptys, then remove it from there it exists
				if _, deleted := realEmptys[entry.Account]; deleted {
					delete(realEmptys, entry.Account)
				}
			}
		}

		// put these deletes into the final set
		for addr := range emptyDeletesThisRound {
			realEmptys[addr] = true
		}
	}
	
	return realEmptys
}


func GetCreatedKeysExported(j [][]state.ExportedJournalEntry) map[state.KeyKey]bool {
	finalSet := make(map[state.KeyKey]bool)
	var zeroVal common.Hash
	zeroVal.SetBytes(nil)

	//targeta := common.HexToAddress("0x52Aa899454998Be5b000Ad077a46Bbe360F4e497")
	//targetk := common.HexToHash("0xd943cec1dfc617bf9515058376abfab0217f98cce018735f02efd4abd3453ad8")

	for _, jn := range j {
		for _, e := range jn {
			switch entry := (e.Entry).(type) {
			case state.StorageChange:
				if e.Reverted {
					continue
				}

				// if the storage slot goes from 0 to non-0 it was created
				//if entry.prevvalue.Cmp(zeroVal) == 0 || entry.newvalue.Cmp(zeroVal) != 0 {
				if entry.Origvalue.Cmp(zeroVal) == 0 && entry.Newvalue.Cmp(zeroVal) != 0 {
					// a storage slot went from not 0 to 0
					//if entry.account.Cmp(targeta) == 0 && entry.key.Cmp(targetk) == 0 {
					//	log.Debug("Created key", "addr", entry.account, "key", entry.key, "orgvalue", entry.origvalue, "prevalue", entry.prevvalue, "newvalue", entry.newvalue)
					//}
					finalSet[state.NewKeyKey(entry.Account, entry.Key)] = true
				} else if entry.Origvalue.Cmp(zeroVal) == 0 {
					// implies orig was 0 and the newval is also 0 so it is no longer "created"
					if _, ok := finalSet[state.NewKeyKey(entry.Account, entry.Key)]; ok {
						delete(finalSet, state.NewKeyKey(entry.Account, entry.Key))
					}
				} else {
					// otherwise it's still 0
					//log.Debug("Storage sot not set", "addr", entry.account, "key", entry.key)
				}
			default:
			}
		}
	}
	return finalSet
}

// given a journal return all the storage trie keys that were queried
// and returned 0 and are never set. This let's us validate that our collected
// data is capturing all keys and we can validate a transition from a prelog to
// a post log
func GetKeysAlwaysZeroExported(j [][]state.ExportedJournalEntry) map[state.KeyKey]bool {
	finalSet := make(map[state.KeyKey]bool)
	for _, jn := range j {
		for _, e := range jn {
			switch entry := (e.Entry).(type) {
			case state.GetStorageEntry:
				k := state.NewKeyKey(entry.Account, entry.Key)
				// we want to check what the return value was
				//if (common.Hash{}).Cmp(entry.value) == 0 {
				if entry.Value.Cmp(common.Hash{}) == 0 {
					var zeroVal common.Hash
					zeroVal.SetBytes(nil)
					if entry.Value.Cmp(zeroVal) != 0 {
						panic("comparison error")
					}
					finalSet[k] = true
				} else {
					_, exists := finalSet[k]
					if exists {
						// this means the account went from zero to not-zero so remove it
						delete(finalSet, k)
					}
				}
			case state.StorageChange:
				var zeroVal common.Hash
				zeroVal.SetBytes(nil)

				k := state.NewKeyKey(entry.Account, entry.Key)
				if entry.Prevvalue.Cmp(zeroVal) != 0 && entry.Newvalue.Cmp(zeroVal) == 0 {
					// if the old value had something and the new one is set to 0
					if entry.Newvalue.Cmp(common.Hash{}) != 0 {
						panic("comparison error")
					}
					//log.Debug("Deleted key", "addr", entry.account, "key", entry.key)
					//finalSet[k] = true
				} else {
					// implcit in this condition is that prevvalue and newvalue can't be
					// the same thing, therefore here it's clear that newvalue != 0
					_, exists := finalSet[k]
					if !exists {
						// it's changed to zero
						delete(finalSet, k)
					}
					//log.Debug("Storage change not set to 0", "addr", entry.account, "key", entry.key)
				}
			default:
			}
		}
	}
	return finalSet
}



