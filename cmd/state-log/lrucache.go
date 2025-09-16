package main

import (
	"container/list"
	"github.com/ethereum/go-ethereum/log"
	_"github.com/ethereum/go-ethereum/common"
	_"github.com/ethereum/go-ethereum/core/state"
)

// cacheNode is a wrapper for a Node struct to be stored in the list.
type cacheNode struct {
	node *Node
}

type LRUCache struct {
	limit    int
	contents map[Node]*list.Element
	hits     int
	misses   int
	list     *list.List
}

// NewLRUCache creates a new LRUCache with the specified limit.
func NewLRUCache(limit int) *LRUCache {
	return &LRUCache{
		limit:    limit,
		contents: make(map[Node]*list.Element),
		list:     list.New(),
		hits:     0,
		misses:   0,
	}
}

// Access is a unified function that gets a Node from the cache or adds it if it's not present.
// It returns the evicted Node if a new Node had to be added and the cache was full.
func (c *LRUCache) Access(n *Node) (*Node, *Node) {
	// First, check if the Node exists in the cache.
	if element, ok := c.contents[*n]; ok {
		c.list.MoveToFront(element)
		c.hits++
		return element.Value.(*cacheNode).node, nil // Return the found node and no evicted node.
	}

	// If the Node is not found, it's a miss.
	c.misses++

	var evicted *Node

	// Check if the cache is full before adding the new Node.
	if c.list.Len() >= c.limit {
		// Get the least recently used node from the back of the list.
		backElement := c.list.Back()
		if backElement != nil {
			evicted = backElement.Value.(*cacheNode).node
		}
	}

	// Now, put the new Node into the cache. The Put method handles the eviction.
	// We've already captured the evicted node, so we don't need the Put method to return it.
	c.Put(n)

	// Return the newly accessed node and the evicted node (if any).
	return n, evicted
}

// Get retrieves a Node from the cache.
func (c *LRUCache) Get(n Node) (*Node, bool) {
	if element, ok := c.contents[n]; ok {
		c.list.MoveToFront(element)
		c.hits++
		return element.Value.(*cacheNode).node, true
	}
	c.misses++
	return nil, false
}

// Put adds or updates a Node in the cache.
func (c *LRUCache) Put(n *Node) {
	if element, ok := c.contents[*n]; ok {
		c.list.MoveToFront(element)
		element.Value.(*cacheNode).node = n
		return
	}

	newNode := &cacheNode{node: n}
	element := c.list.PushFront(newNode)
	c.contents[*n] = element

	if c.list.Len() > c.limit {
		backElement := c.list.Back()
		if backElement != nil {
			c.list.Remove(backElement)
			nodeToRemove := backElement.Value.(*cacheNode).node
			delete(c.contents, *nodeToRemove)
		}
	}
}

// Contains checks if a Node is present in the cache.
// It does not update the LRU order or metrics.
func (c *LRUCache) Contains(n Node) bool {
	_, ok := c.contents[n]
	return ok
}

// PrintState logs the current state of the LRU cache.
// It reports the hit and miss counts, the cache limit, and the number of items.
func (c *LRUCache) PrintState() {
	log.Info("LRU Cache State",
		"hits", c.hits,
		"misses", c.misses,
		"limit", c.limit,
		"size", c.list.Len(),
	)
}
