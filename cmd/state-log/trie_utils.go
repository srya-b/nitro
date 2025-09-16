package main 

import (
//	"fmt"
//
	"github.com/ethereum/go-ethereum/common"
//	"github.com/ethereum/go-ethereum/trie"
//	"github.com/ethereum/go-ethereum/log"
)

type Leaf struct {
	// if it's an account, then ha is all zeros
	// if it's a storage slot ha is the hashed address key
	ha		common.Hash 
	// if it's an account, this is the hashed address key
	// if it's a storage slot this is the hashed key
	hk		common.Hash
}
