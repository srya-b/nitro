package main

import (
	"fmt"
	"sort"
	_"math"
)

// WeightedVertexGraph now represents a Directed Acyclic Graph (DAG)
// with immutable weights on each vertex.
type WeightedVertexGraph struct {
	Adj           map[int][]int
	VertexWeights map[int]uint64 // Added: Stores weight for each vertex
	BlockNo       int
}

// Note: 'Conflict' and 'Edge' structs are assumed to be identical
// to the ones in your other file, so they don't need to be redefined
// or renamed.

// NewWeightedVertexGraph creates a new WeightedVertexGraph.
// It creates N vertices (0 to N-1) where N is the length of the weights slice.
// Each vertex i is assigned weights[i].
func NewWeightedVertexGraph(weights []uint64, blockNumber int) WeightedVertexGraph {
	n := len(weights)
	adj := make(map[int][]int, n)
	vWeights := make(map[int]uint64, n)

	for i := 0; i < n; i++ {
		adj[i] = []int{}
		vWeights[i] = weights[i] // Assign weight at creation
	}

	return WeightedVertexGraph{
		Adj:           adj,
		VertexWeights: vWeights, // Store the weights
		BlockNo:       blockNumber,
	}
}

// HasSameVertices checks if two WeightedVertexGraphs contain the exact same set of vertex indices.
func (g *WeightedVertexGraph) HasSameVertices(other *WeightedVertexGraph) (bool, []int, []int) {
	gOnly := make([]int, 0)
	otherOnly := make([]int, 0)

	// 1. Create check maps
	otherVertices := make(map[int]bool)
	for v := range other.Adj {
		otherVertices[v] = true
	}
	gVertices := make(map[int]bool)
	for v := range g.Adj {
		gVertices[v] = true
	}

	// 2. Find vertices in g but not in other (gOnly)
	for v := range g.Adj {
		if !otherVertices[v] {
			gOnly = append(gOnly, v)
		}
	}

	// 3. Find vertices in other but not in g (otherOnly)
	for v := range other.Adj {
		if !gVertices[v] {
			otherOnly = append(otherOnly, v)
		}
	}

	// Sort the output slices for consistent results
	sort.Ints(gOnly)
	sort.Ints(otherOnly)

	isSame := len(gOnly) == 0 && len(otherOnly) == 0
	return isSame, gOnly, otherOnly
}

// IsEqual checks if two WeightedVertexGraphs are identical (vertices, edges, AND vertex weights).
func (g *WeightedVertexGraph) IsEqual(other *WeightedVertexGraph) (bool, []Edge) {
	gOnlyEdges := make([]Edge, 0)

	// 1. Check for same vertices
	isSameVertices, gOnlyV, otherOnlyV := g.HasSameVertices(other)
	if !isSameVertices {
		fmt.Printf("Warning: IsEqual aborted. Vertices differ (G only: %v, Other only: %v). Returning false.\n", gOnlyV, otherOnlyV)
		return false, gOnlyEdges
	}

	// 2. Check for differing vertex weights
	for v, gWeight := range g.VertexWeights {
		if otherWeight, ok := other.VertexWeights[v]; !ok || gWeight != otherWeight {
			// Vertex exists in both, but weight differs (or missing in other, though HasSameVertices should catch)
			fmt.Printf("Warning: IsEqual aborted. Vertex %d has different weights (%d vs %d). Returning false.\n", v, gWeight, otherWeight)
			return false, gOnlyEdges
		}
	}

	// 3. Check for differing edges
	for u, gNeighbors := range g.Adj {
		otherNeighbors := other.Adj[u]

		otherNeighborMap := make(map[int]bool)
		for _, v := range otherNeighbors {
			otherNeighborMap[v] = true
		}

		// Check for edges in g but not in other
		for _, v := range gNeighbors {
			if !otherNeighborMap[v] {
				gOnlyEdges = append(gOnlyEdges, Edge{U: u, V: v})
			}
		}
	}

	// 4. Return result
	isEqual := len(gOnlyEdges) == 0
	return isEqual, gOnlyEdges
}

// AddEdge adds a directed edge U -> V. It first checks for cycles.
func (g WeightedVertexGraph) AddEdge(u, v int) error {
	// 1. Basic Existence Checks
	if _, ok := g.Adj[u]; !ok {
		return fmt.Errorf("vertex %d does not exist in the graph", u)
	}
	if _, ok := g.Adj[v]; !ok {
		return fmt.Errorf("vertex %d does not exist in the graph", v)
	}

	//// 2. Check for Acyclicity (Cycle Detection)
	//if g.canReach(v, u) {
	//	return fmt.Errorf("cannot add directed edge %d -> %d: adding this edge creates a cycle", u, v)
	//}

	// 3. Check for Duplicate Edge (since it's a slice)
	if contains(g.Adj[u], v) {
		return nil // Edge already exists, no error
	}

	// 4. Add the directed edge: U -> V
	g.Adj[u] = append(g.Adj[u], v)
	sort.Ints(g.Adj[u]) // Keep list sorted

	return nil
}

// RemoveEdge removes the directed edge U -> V.
func (g WeightedVertexGraph) RemoveEdge(u, v int) error {
	// 1. Existence Checks
	if _, ok := g.Adj[u]; !ok {
		return fmt.Errorf("start vertex %d does not exist in the graph", u)
	}

	// 2. Remove V from U's adjacency list (U -> V)
	var found bool
	g.Adj[u], found = removeElement(g.Adj[u], v)

	if !found {
		return fmt.Errorf("edge %d -> %d does not exist", u, v)
	}

	return nil
}

// FiniteCores adds directed edges based on the core dependency rule: j -> i.
func (g WeightedVertexGraph) FiniteCores(K int) {
	if K < 0 {
		fmt.Println("Warning: K must be non-negative for FiniteCores logic. No edges added.")
		return
	}

	N := g.NumVertices()
	if N == 0 || N <= K {
		return
	}

	// Iterate through all unique pairs (i, j) where i < j
	for i := 0; i < N; i++ {
		for j := i + 1; j < N; j++ {
			// Apply the dependency rule: i + K <= j
			if i+K <= j {
				// ADD DIRECTED EDGE: j -> i
				err := g.AddEdge(j, i)
				if err != nil {
					fmt.Printf("Warning: Failed to add edge %d -> %d due to cycle: %v\n", j, i, err)
					panic("")
				}
			}
		}
	}
}

// canReach determines if there is a directed path from 'start' to 'target'.
func (g WeightedVertexGraph) canReach(start, target int) bool {
	visited := make(map[int]bool)
	stack := []int{start} // Use stack for DFS

	for len(stack) > 0 {
		u := stack[len(stack)-1]
		stack = stack[:len(stack)-1] // Pop

		if u == target {
			return true
		}

		if !visited[u] {
			visited[u] = true
			for _, v := range g.Adj[u] {
				if !visited[v] {
					stack = append(stack, v)
				}
			}
		}
	}
	return false
}

// LongestPathInDAG calculates the longest path in the DAG by *edge count*.
func (g WeightedVertexGraph) LongestPathInDAG() int {
	N := g.NumVertices()
	if N == 0 {
		return -1
	}
	
	hasEdges := false
	for _, neighbors := range g.Adj {
		if len(neighbors) > 0 {
			hasEdges = true; break
		}
	}
	if !hasEdges && N > 0 { return 0 }
	
	distances := make(map[int]int)
	maxDistance := 0

	for vertex := range g.Adj {
		pathLength := g.dfsLongestPath(vertex, distances)
		if pathLength > maxDistance {
			maxDistance = pathLength
		}
	}

	return maxDistance
}

// dfsLongestPath is a helper for finding the longest path (by *edge count*) from 'u'.
func (g WeightedVertexGraph) dfsLongestPath(u int, distances map[int]int) int {
	if dist, ok := distances[u]; ok {
		return dist // Return memoized result
	}

	maxPath := 0
	for _, v := range g.Adj[u] {
		pathLength := 1 + g.dfsLongestPath(v, distances)
		if pathLength > maxPath {
			maxPath = pathLength
		}
	}

	distances[u] = maxPath
	return maxPath
}

type PathInfo struct {
	length int    // Number of edges in the path
	weight uint64 // Sum of vertex weights in the path
}

// Rather than giving the path with the largest weight, this returns the weight on the 
// longest path in the graph (longest by number of edges)
func (g WeightedVertexGraph) MaxWeightedVertexPath() uint64 {
	N := g.NumVertices()
	if N == 0 {
		return 0
	}

	// Memoization table for vertex weight paths
	memo := make(map[int]PathInfo)
	
	// This will track the best path *found so far* from *any* starting vertex
	bestOverallPath := PathInfo{length: -1, weight: 0}

	// Find the heaviest path starting from every vertex
	for vertex := range g.Adj {
		pathFromVertex := g.dfsMaxVertexWeightPath(vertex, memo)

		if pathFromVertex.length > bestOverallPath.length {
			// This path is longer than any other starting path seen
			bestOverallPath = pathFromVertex
		} else if pathFromVertex.length == bestOverallPath.length {
			// Same max length, check if this one is heavier
			if pathFromVertex.weight > bestOverallPath.weight {
				bestOverallPath = pathFromVertex
			}
		}
	}

	return bestOverallPath.weight
}

func (g WeightedVertexGraph) dfsMaxVertexWeightPath(u int, memo map[int]PathInfo) PathInfo {
	if info, ok := memo[u]; ok {
		return info // Return memoized result
	}

	// 1. Find the best path starting *from a neighbor*
	// We prioritize max length, then max weight.
	// Start with length -1 to distinguish from a leaf's 0-length path.
	bestNeighborPath := PathInfo{length: -1, weight: 0}

	for _, v := range g.Adj[u] {
		// Get the best path *from neighbor v*
		neighborPath := g.dfsMaxVertexWeightPath(v, memo)

		if neighborPath.length > bestNeighborPath.length {
			// This path is longer, it's the new best
			bestNeighborPath = neighborPath
		} else if neighborPath.length == bestNeighborPath.length {
			// Same length, check if this path is heavier
			if neighborPath.weight > bestNeighborPath.weight {
				bestNeighborPath = neighborPath
			}
		}
	}

	// 2. Create the path info for node 'u' based on the best neighbor path
	var myPath PathInfo
	if bestNeighborPath.length == -1 {
		// This means 'u' is a leaf node (no neighbors).
		// The path is just 'u' itself.
		myPath = PathInfo{
			length: 0, // No *edges*
			weight: g.VertexWeights[u],
		}
	} else {
		// This means 'u' is not a leaf node.
		// The path from 'u' is 1 edge + neighbor's path
		myPath = PathInfo{
			length: 1 + bestNeighborPath.length,
			weight: g.VertexWeights[u] + bestNeighborPath.weight,
		}
	}

	memo[u] = myPath
	return myPath
}

func (g WeightedVertexGraph) TotalVertexWeight() uint64 {
	var total uint64 = 0
	for _, weight := range g.VertexWeights {
		total += weight
	}
	return total
}


// --- Renamed & Replaced Functions ---

// Diameter and MaxPath still point to the *edge count* version.
func (g WeightedVertexGraph) Diameter() int {
	return g.LongestPathInDAG()
}

func (g WeightedVertexGraph) MaxPath() int {
	return g.LongestPathInDAG()
}


// --- Remaining Helper Functions (Updated) ---

func (g WeightedVertexGraph) NumVertices() int { /* ... */ return len(g.Adj) }

func (g WeightedVertexGraph) Copy() WeightedVertexGraph {
	// Copy Adj list
	newAdj := make(map[int][]int, len(g.Adj))
	for vertex, neighbors := range g.Adj {
		newNeighbors := make([]int, len(neighbors))
		copy(newNeighbors, neighbors)
		newAdj[vertex] = newNeighbors
	}
	
	// Copy Vertex Weights
	newWeights := make(map[int]uint64, len(g.VertexWeights))
	for vertex, weight := range g.VertexWeights {
		newWeights[vertex] = weight
	}

	return WeightedVertexGraph{
		BlockNo:       g.BlockNo,
		Adj:           newAdj,
		VertexWeights: newWeights,
	}
}

func (g WeightedVertexGraph) Display(name string) {
	fmt.Printf("-- %s (BlockNo: %d, Vertices: %d) --\n", name, g.BlockNo, g.NumVertices())
	var vertices []int
	for v := range g.Adj {
		vertices = append(vertices, v)
	}
	sort.Ints(vertices)
	for _, v := range vertices {
		// Print vertex and its weight
		fmt.Printf("Vertex %d (Weight: %d): %v\n", v, g.VertexWeights[v], g.Adj[v])
	}
}

// Note: 'contains' and 'removeElement' helpers are assumed to
// be present in the package from your original file.

// func contains(slice []int, item int) bool {
// 	for _, a := range slice { if a == item { return true } }
// 	return false
// }
// func removeElement(slice []int, val int) ([]int, bool) {
// 	for i, v := range slice {
// 		if v == val { slice[i] = slice[len(slice)-1]; return slice[:len(slice)-1], true }
// 	}
// 	return slice, false
// }

func (g WeightedVertexGraph) Dependency(vertex int) ([]int, error) {
	neighbors, ok := g.Adj[vertex]
	if !ok { return nil, fmt.Errorf("vertex %d does not exist in the graph", vertex) }
	result := make([]int, len(neighbors)); copy(result, neighbors)
	return result, nil
}

// HeaviestPath finds the path with the maximum possible sum of vertex weights.
// This function prioritizes weight *only*, unlike MaxWeightedVertexPath
// which prioritizes edge-count (length) first.
func (g WeightedVertexGraph) HeaviestPath() uint64 {
	N := g.NumVertices()
	if N == 0 {
		return 0
	}

	// memo stores the calculated heaviest path weight *starting* from a given vertex.
	memo := make(map[int]uint64, N)
	var maxOverallWeight uint64 = 0

	// We must check the heaviest path starting from *every* vertex,
	// because the globally heaviest path might be in a subgraph
	// not reachable from the start of another, lighter-but-longer path.
	for vertex := range g.Adj {
		pathWeight := g.dfsHeaviestPath(vertex, memo)
		if pathWeight > maxOverallWeight {
			maxOverallWeight = pathWeight
		}
	}

	return maxOverallWeight
}

// dfsHeaviestPath is a memoized DFS helper for HeaviestPath.
// It returns the weight of the heaviest path *starting* from vertex 'u'.
func (g WeightedVertexGraph) dfsHeaviestPath(u int, memo map[int]uint64) uint64 {
	// 1. Check memoization table
	// If we've already calculated the heaviest path from 'u', return it.
	if weight, ok := memo[u]; ok {
		return weight
	}

	// 2. Find the max weight of any path starting from a neighbor
	var maxNeighborWeight uint64 = 0
	for _, v := range g.Adj[u] {
		// Recursively find the heaviest path starting from neighbor 'v'
		neighborWeight := g.dfsHeaviestPath(v, memo)

		// Find the neighbor that leads to the heaviest possible path
		if neighborWeight > maxNeighborWeight {
			maxNeighborWeight = neighborWeight
		}
	}

	// 3. The heaviest path from 'u' is its own weight plus the heaviest
	//    path that starts from one of its neighbors.
	//    If 'u' is a leaf node (no neighbors), maxNeighborWeight will be 0,
	//    and the path is just its own weight.
	myPathWeight := g.VertexWeights[u] + maxNeighborWeight

	// 4. Store in memo and return
	memo[u] = myPathWeight
	return myPathWeight
}

// Example main, renamed to avoid conflict
//func main_weighted_vertex() {
//	// Use the new constructor: NewWeightedVertexGraph(weights []uint64, blockNumber int)
//	N := 5
//	weights1 := make([]uint64, N)
//	for i := 0; i < N; i++ { weights1[i] = 10 }
//	graph := NewWeightedVertexGraph(weights1, 100)
//
//	fmt.Println("--- DAG Test 1: Simple Path and Cycle Check ---")
//
//	graph.AddEdge(0, 1)
//	graph.AddEdge(1, 2)
//
//	graph.Display("DAG 0->1->2")
//
//	// MaxPath: 0 -> 1 -> 2 (Length 2, by *edge count*)
//	fmt.Printf("Max Path Length (Edges) (Expected 2): %d\n", graph.MaxPath())
//	// MaxWeightedVertexPath: 0 -> 1 -> 2 (Weights 10+10+10 = 30)
//	fmt.Printf("Max Path Weight (Vertex Sum) (Expected 30): %d\n", graph.MaxWeightedVertexPath())
//}
