package main

import (
	"encoding/json"
	"fmt"
	"io/ioutil"
	"math/big"
	"os"

	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/log"
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
