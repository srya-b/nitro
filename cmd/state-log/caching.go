package main

import (
	"github.com/ethereum/go-ethereum/common"
	_"github.com/ethereum/go-ethereum/core/state"
)

type Cache struct {
	Limit 		int
	Contents    []common.Hash
	hits   		int
	misses		int
}

func NewCache(n int) *Cache {
	return &Cache{
			Limit: n,
	}
}

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
	addr	common.Address
	key		common.Hash
}
	


// read through the journal and get the accesses
//func AccessListForValidation(preObj *state.PreLog) []Access {
//	var accesses []Access
//	// we only care about the final shape of the access after the transaction is complete
//	// therefore, we iterate through the journal in reverse so that nodes that are accessed
//	// multiple times will be in their final position (because their first appearance in 
//	// reverse order is their final position in the cache)
//	for i := 0; i < len(preObj.Journals); i++ {
//		journal := state.JournalToExported(preObj.Journals[i])
//		
//
//	}
//
//	return true
//}
