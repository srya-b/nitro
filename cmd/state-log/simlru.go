package main

import (
	"fmt"
	"github.com/ethereum/go-ethereum/log"
)

type LRUSim struct {
	cache *LRUCache
}


func NewLRUSim(limit int) *LRUSim {
	return &LRUSim{
		cache: NewLRUCache(limit),
	}
}

func (s *LRUSim) Run(dir string) {
	logFiles := getLogFilesSorted(dir)

	for j := 0; j < len(logFiles); j++ {
		if j > 100 {
			break
		}
		for i := 0; i < len(logFiles[j]) - 1; i += 2 {
			pre := logFiles[j][i]
			post := logFiles[j][i+1]
			if pre.Type == PRE && post.Type == POST {
				preObj, exists := getPreObj(pre.Blockno, pre.Count)
				if !exists {
					log.Error("First preLog should exist")
					break
				}
				postObj, exists := getPostObj(post.Blockno, post.Count)
				if !exists {
					log.Error("Post obj shoudl never not exist, only preObj shouldn't exist", "block", post.Blockno, "count", post.Count)
					panic("")
				}
				
				if ignoreJournal(preObj.Journals) {
					log.Info("An empty journal is valid.")
					continue
				}

				ok := CheckRoot(preObj)
				if !ok {
					_, exists := postObj.AccountNodes[preObj.Root]
					if !exists {
						panic("Root isn't in the postlog either")
					}
					log.Debug("Don't work this block preLog is empty")
					continue
				}

				accesses := AccessesForValidation(preObj)
				log.Info("Accesses", "l", len(accesses))
				s.PreLogAccesses(accesses)
				post_accesses := OrderedAccessesForPostLog(preObj, postObj)
				s.PostLogAccesses(post_accesses)
			} else {
				panic(fmt.Sprintf("weird logfiles: %v", logFiles[j]))
			}
			break
		}
	}
}

func (s *LRUSim) RunRecordTxBytes(dir string) {
	logFiles := getLogFilesSorted(dir)

	for j := 0; j < len(logFiles); j++ {
		if j > 100 {
			break
		}
		for i := 0; i < len(logFiles[j]) - 1; i += 1 {
			pre := logFiles[j][i]
			post := logFiles[j][i+1]
			if pre.Type == PRE && post.Type == POST {
				preObj, exists := getPreObj(pre.Blockno, pre.Count)
				if !exists {
					log.Error("First preLog should exist")
					break
				}
				postObj, exists := getPostObj(post.Blockno, post.Count)
				if !exists {
					log.Error("Post obj shoudl never not exist, only preObj shouldn't exist", "block", post.Blockno, "count", post.Count)
					panic("")
				}
				
				if ignoreJournal(preObj.Journals) {
					log.Info("An empty journal is valid.")
					continue
				}

				ok := CheckRoot(preObj)
				if !ok {
					_, exists := postObj.AccountNodes[preObj.Root]
					if !exists {
						panic("Root isn't in the postlog either")
					}
					log.Debug("Don't work this block preLog is empty")
					continue
				}

				accesses, sizes, txNodes := AccessesForValidationTxBytes(preObj)
				log.Info("Accesses", "l", len(accesses))
				bytesMissingPerTx := s.PreLogAccessesTxBytes(accesses, sizes, txNodes)
				_ = bytesMissingPerTx
				//log.Info("Bytes missing per Tx", "l", bytesMissingPerTx)
				post_accesses := OrderedAccessesForPostLog(preObj, postObj)
				s.PostLogAccesses(post_accesses)
			} else {
				panic(fmt.Sprintf("weird logfiles: %v", logFiles[j]))
			}
			break
		}
	}
}

func (s *LRUSim) RunRecordBlockBytes(dir string) {
	logFiles := getLogFilesSorted(dir)
	bytesMissingPerBlock := []int{}
	for j := 0; j < len(logFiles); j++ {
		if j > 10000 {
			break
		}
		bytesForBlock := 0
		for i := 0; i < len(logFiles[j]) - 1; i += 1 {
			pre := logFiles[j][i]
			post := logFiles[j][i+1]
			if pre.Type == PRE && post.Type == POST {
				preObj, exists := getPreObj(pre.Blockno, pre.Count)
				if !exists {
					log.Error("First preLog should exist")
					break
				}
				postObj, exists := getPostObj(post.Blockno, post.Count)
				if !exists {
					log.Error("Post obj shoudl never not exist, only preObj shouldn't exist", "block", post.Blockno, "count", post.Count)
					panic("")
				}
				
				if ignoreJournal(preObj.Journals) {
					//log.Info("An empty journal is valid.")
					continue
				}

				ok := CheckRoot(preObj)
				if !ok {
					_, exists := postObj.AccountNodes[preObj.Root]
					if !exists {
						panic("Root isn't in the postlog either")
					}
					//log.Debug("Don't work this block preLog is empty")
					continue
				}

				accesses, sizes := AccessesForValidationWithBytes(preObj)
				//log.Info("Accesses", "l", len(accesses))
				bytesMissing := s.PreLogAccessesBlockBytes(accesses, sizes)
				bytesForBlock += bytesMissing
				//log.Info("Bytes missing per Tx", "l", bytesMissingPerTx)
				post_accesses := OrderedAccessesForPostLog(preObj, postObj)
				s.PostLogAccesses(post_accesses)
			} else {
				panic(fmt.Sprintf("weird logfiles: %v", logFiles[j]))
			}
			break
		}
		bytesMissingPerBlock = append(bytesMissingPerBlock, bytesForBlock)
	}
	//log.Info("Bytes missing per block", "bytes", bytesMissingPerBlock)
	BlockBytesHistogramWriteFile(bytesMissingPerBlock, 10000)
}

func (s *LRUSim) PreLogAccesses(accesses map[Node]bool) {
	for n := range accesses {
		s.cache.Access(&n)
	}

	log.Info("PreLog accesses")
	//s.cache.PrintState()
}

func (s *LRUSim) PreLogAccessesTxBytes(accesses map[Node]bool, sizes map[Node]int, txNodes [][]Node) []int {
	seen := make(map[Node]bool)
	perTxBytes := []int{}
	// iterate perTx rather than over accesses
	// the goal is to still do accesses like touching each node once
	// but we want to know in order to collect the missing bytes
	for _, nodes := range txNodes {
		txBytes := 0
		for _, n := range nodes {
			_, ok := seen[n]
			if ok {
				// then we ignore this
				continue
			}

			// otherwise to the access and log the bytes 
			numBytes, ok := sizes[n]
			if !ok {
				log.Error("Accessing a node that has no bytes", "n", n)
				panic("")
			}

			if numBytes == 0 {
				// skip this node
				continue
			}

			_, _, bytesMissing := s.cache.AccessWithBytes(&n, sizes)
			txBytes += bytesMissing
		}
		// add the bytes for this transaction
		perTxBytes = append(perTxBytes, txBytes)
	}

	log.Info("PreLog accesses")
	//s.cache.PrintState()
	return perTxBytes
}

func (s *LRUSim) PreLogAccessesBlockBytes(accesses map[Node]bool, sizes map[Node]int) int {
	totalBytes := 0
	for n := range accesses {
		numBytes, ok := sizes[n]
		if !ok {
			log.Error("Accessing a node that has no bytes", "n", n)
			panic("")
		}

		if numBytes == 0 {
			// skip this node
			continue
		}
		_, _, bytesMissing := s.cache.AccessWithBytes(&n, sizes)
		totalBytes += bytesMissing
	}

	//log.Info("postlog accesses")
	//s.cache.PrintState()
	return totalBytes
}

func (s *LRUSim) PostLogAccesses(accesses []Node) {
	for _, n := range accesses {
		s.cache.Access(&n)
	}

	//log.Info("postlog accesses")
	//s.cache.PrintState()
}

func (s *LRUSim) accessesInMap(accesses map[Node]bool) {
	// do the accesses in the LRU cache
	hits := 0
	misses := 0
	for n := range accesses {
		if s.cache.Contains(n) {
			hits++
		} else {
			misses++
		}
	}	

	log.Info("Hits and misses", "hits", hits, "misses", misses)
}

