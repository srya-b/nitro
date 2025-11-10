package main

import (
	"fmt"
	"sort"
	_"math"
)

// DependencyGraph now represents a Directed Acyclic Graph (DAG).
// U -> V means V is a dependency of U, or U points to V.
type DependencyGraph struct {
	Adj map[int][]int 
	BlockNo int       
}

type Conflict struct {
	tx1 int
	tx2 int
}

// Edge is a simple struct to represent a directed edge (U -> V).
type Edge struct {
	U int
	V int
}

// NewDependencyGraph creates a new DependencyGraph.
func NewDependencyGraph(n int, blockNumber int) DependencyGraph {
    // ... (unchanged)
	adj := make(map[int][]int, n)
	for i := 0; i < n; i++ {
		adj[i] = []int{}
	}
	return DependencyGraph{
        Adj:     adj,
        BlockNo: blockNumber,
	}
}

// HasSameVertices checks if two DependencyGraphs contain the exact same set of vertex indices.
// It now accepts graph POINTERS.
// Returns: (isSame, verticesInSelfOnly, verticesInOtherOnly)
func (g *DependencyGraph) HasSameVertices(other *DependencyGraph) (bool, []int, []int) {
    gOnly := make([]int, 0)
    otherOnly := make([]int, 0)
    
    // 1. Create check maps
    otherVertices := make(map[int]bool)
    for v := range other.Adj { // Accessing .Adj directly works with pointers
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

// IsEqual checks if two DependencyGraphs are identical (same vertices and same edges).
// It now accepts graph POINTERS.
// Returns: (isEqual, edgesInSelfButNotOther)
func (g *DependencyGraph) IsEqual(other *DependencyGraph) (bool, []Edge) {
    gOnlyEdges := make([]Edge, 0)
    
    // 1. Check for same vertices first, passing pointers
    isSameVertices, gOnlyV, otherOnlyV := g.HasSameVertices(other)
    if !isSameVertices {
        fmt.Printf("Warning: IsEqual aborted. Vertices differ (G only: %v, Other only: %v). Returning false.\n", gOnlyV, otherOnlyV)
        return false, gOnlyEdges
    }

    // 2. Check for differing edges
    for u, gNeighbors := range g.Adj {
        otherNeighbors := other.Adj[u] // Accessing .Adj works on pointers

        // Create a quick check map for 'other' neighbors
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
    
    // 3. Return result
    isEqual := len(gOnlyEdges) == 0
    return isEqual, gOnlyEdges
}

// AddEdge adds a directed edge U -> V. It first checks for cycles.
func (g DependencyGraph) AddEdge(u, v int) error {
	// 1. Basic Existence Checks
	if _, ok := g.Adj[u]; !ok {
		return fmt.Errorf("vertex %d does not exist in the graph", u)
	}
	if _, ok := g.Adj[v]; !ok {
		return fmt.Errorf("vertex %d does not exist in the graph", v)
	}
    
    // 2. Check for Acyclicity (Cycle Detection)
    // A cycle exists if adding U -> V means V can already reach U.
    if g.canReach(v, u) {
        return fmt.Errorf("cannot add directed edge %d -> %d: adding this edge creates a cycle", u, v)
    }

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
func (g DependencyGraph) RemoveEdge(u, v int) error {
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

// FiniteCores adds directed edges based on the core dependency rule: j -> i (since i < j).
// Edge is added if i + K <= j, but the direction is j -> i.
func (g DependencyGraph) FiniteCores(K int) {
    // ... (Existence and setup logic remains similar)
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
            if i + K <= j {
                // ADD DIRECTED EDGE: j -> i (from larger index to smaller index)
                
                // Note: AddEdge already handles existence, sorting, and cycle checking.
                // In this case, since j > i, adding j -> i cannot create an immediate cycle,
                // but it could still complete a larger cycle.
                err := g.AddEdge(j, i)
                if err != nil {
                    // This error indicates a cycle was formed by the dependency chain.
                    // We print a warning and continue, as the function should add as many as possible.
                    fmt.Printf("Warning: Failed to add edge %d -> %d due to cycle: %v\n", j, i, err)
					panic("")
                }
            }
        }
    }
}

// canReach determines if there is a directed path from 'start' to 'target'.
// This uses DFS and is the core of the cycle check.
func (g DependencyGraph) canReach(start, target int) bool {
    // Note: We perform a search *before* adding the edge U -> V.
    // If V can reach U, then U -> V completes the cycle.
    
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
            // Push unvisited neighbors onto the stack
            for _, v := range g.Adj[u] {
                if !visited[v] {
                    stack = append(stack, v)
                }
            }
        }
    }
    return false
}

// LongestPathInDAG calculates the longest path in the DAG.
// This is the correct calculation for DAG diameter.
// Returns:
//   - The length of the longest path.
//   - -1 if the graph is empty.
func (g DependencyGraph) LongestPathInDAG() int {
    N := g.NumVertices()
    if N == 0 {
        return -1
    }
    
    // 1. Calculate the topological order or iterate in index order if simple
    // Since we are iterating through all vertices, we can skip explicit topological sort
    // and rely on DFS/Memoization for efficiency.
    
    distances := make(map[int]int)
    maxDistance := 0

    // Find the longest path starting from every vertex
    for vertex := range g.Adj {
        pathLength := g.dfsLongestPath(vertex, distances)
        if pathLength > maxDistance {
            maxDistance = pathLength
        }
    }

    return maxDistance
}

// dfsLongestPath is a recursive helper with memoization for finding the longest path from 'u'.
func (g DependencyGraph) dfsLongestPath(u int, distances map[int]int) int {
    if dist, ok := distances[u]; ok {
        return dist // Return memoized result
    }

    maxPath := 0
    // Recurse on all children (dependencies)
    for _, v := range g.Adj[u] {
        pathLength := g.dfsLongestPath(v, distances)
        if pathLength > maxPath {
            maxPath = pathLength
        }
    }
    
    // Longest path from u is 1 + max path from its children
    distances[u] = 1 + maxPath
    
    return distances[u]
}

// --- Renamed & Replaced Functions ---

// Diameter is replaced by LongestPathInDAG (since Diameter is often used for shortest paths).
// NOTE: MaxPath will also call LongestPathInDAG.
func (g DependencyGraph) Diameter() int {
    return g.LongestPathInDAG()
}

func (g DependencyGraph) MaxPath() int {
    return g.LongestPathInDAG()
}


// --- Remaining Helper Functions ---

func (g DependencyGraph) NumVertices() int { /* ... */ return len(g.Adj) }
func (g DependencyGraph) Copy() DependencyGraph { 
    newGraph := DependencyGraph{BlockNo: g.BlockNo, Adj: make(map[int][]int, len(g.Adj))}
    for vertex, neighbors := range g.Adj {
        newNeighbors := make([]int, len(neighbors))
        copy(newNeighbors, neighbors) 
        newGraph.Adj[vertex] = newNeighbors
    }
    return newGraph
}
func (g DependencyGraph) Display(name string) { 
	fmt.Printf("-- %s (BlockNo: %d, Vertices: %d) --\n", name, g.BlockNo, g.NumVertices())
	var vertices []int; for v := range g.Adj { vertices = append(vertices, v) }; sort.Ints(vertices)
	for _, v := range vertices { fmt.Printf("Vertex %d: %v\n", v, g.Adj[v]) }
}
func contains(slice []int, item int) bool {
	for _, a := range slice { if a == item { return true } }
	return false
}
func removeElement(slice []int, val int) ([]int, bool) {
	for i, v := range slice {
		if v == val { slice[i] = slice[len(slice)-1]; return slice[:len(slice)-1], true }
	}
	return slice, false
}
func (g DependencyGraph) Dependency(vertex int) ([]int, error) {
	neighbors, ok := g.Adj[vertex]
	if !ok { return nil, fmt.Errorf("vertex %d does not exist in the graph", vertex) }
    result := make([]int, len(neighbors)); copy(result, neighbors)
	return result, nil
}

//func main() {
//    N := 5
//    graph := NewDependencyGraph(N, 100)
//    
//    fmt.Println("--- DAG Test 1: Simple Path and Cycle Check ---")
//    
//    // Add a simple directed path: 0 -> 1 -> 2
//    graph.AddEdge(0, 1)
//    graph.AddEdge(1, 2)
//    
//    graph.Display("DAG 0->1->2")
//    
//    // MaxPath: 0 -> 1 -> 2 (Length 2)
//    fmt.Printf("Max Path Length (Expected 2): %d\n", graph.MaxPath())
//    
//    // Attempt to add a cycle: 2 -> 0
//    err := graph.AddEdge(2, 0)
//    if err != nil {
//        fmt.Printf("\nAttempting 2 -> 0 (Cycle Expected Error): %v\n", err)
//    }
//    
//    fmt.Println("\n--- DAG Test 2: FiniteCores (j -> i) ---")
//    N = 4
//    graph2 := NewDependencyGraph(N, 200)
//    K := 1
//    
//    graph2.FiniteCores(K) // j -> i if i + 1 <= j. This means j = i + 1. (3->2, 2->1, 1->0)
//    
//    graph2.Display("DAG FiniteCores(K=1)")
//    // MaxPath: 3 -> 2 -> 1 -> 0 (Length 3)
//    fmt.Printf("Max Path Length (Expected 3): %d\n", graph2.MaxPath())
//}
