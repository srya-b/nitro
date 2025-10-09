package main

import (
	"fmt"
	"sort"
	"math"
)

// DependencyGraph represents an undirected graph using an adjacency list.
type DependencyGraph struct {
	// Adj represents the adjacency list: map[vertex] -> []neighbors
	Adj map[int][]int 
    // BlockNo is a custom member added to the struct
	BlockNo int       
}

type Conflict struct {
	tx1 int
	tx2 int
}

// NewDependencyGraph creates a new DependencyGraph with 'n' vertices (0 to n-1) 
// but does NOT initialize any edges.
func NewDependencyGraph(n int, blockNumber int) DependencyGraph {
	adj := make(map[int][]int, n)
	for i := 0; i < n; i++ {
		adj[i] = []int{}
	}
	return DependencyGraph{
        Adj:     adj,
        BlockNo: blockNumber,
	}
}

// Copy returns a deep copy of the DependencyGraph.
func (g DependencyGraph) Copy() DependencyGraph {
    // 1. Copy the top-level struct fields
    newGraph := DependencyGraph{
        BlockNo: g.BlockNo,
        Adj:     make(map[int][]int, len(g.Adj)),
    }

    // 2. Perform a deep copy of the adjacency list (Adj map)
    for vertex, neighbors := range g.Adj {
        // Create a new slice for the neighbors to prevent sharing memory.
        newNeighbors := make([]int, len(neighbors))
        // Copy the content of the slice
        copy(newNeighbors, neighbors) 
        
        // Add the new vertex and its copied neighbor slice to the new graph's map
        newGraph.Adj[vertex] = newNeighbors
    }

    return newGraph
}

// NumVertices returns the total count of vertices in the graph.
func (g DependencyGraph) NumVertices() int {
    // The number of vertices is equal to the number of entries in the adjacency map.
	return len(g.Adj)
}

// MaxPath calculates the longest path in the graph, assuming the graph is acyclic (a tree or forest).
// It now calls the updated Diameter function.
func (g DependencyGraph) MaxPath() int {
    // For acyclic unweighted graphs (forests), the longest path is the max diameter of its components.
    return g.Diameter()
}

// Diameter calculates the maximum diameter among all connected components of the graph.
// Returns:
//   - The length of the longest path in the entire graph (i.e., the largest component diameter).
//   - 0 if the graph is empty or has only isolated nodes (max diameter is 0).
func (g DependencyGraph) Diameter() int {
    vertices := make([]int, 0, len(g.Adj))
    for v := range g.Adj {
        vertices = append(vertices, v)
    }
    
    if len(vertices) == 0 {
        return 0
    }
    if len(vertices) == 1 {
        return 0
    }

    maxForestDiameter := 0
    visited := make(map[int]bool)
    
    // Iterate over all vertices to find and process each connected component
    for _, startNode := range vertices {
        if !visited[startNode] {
            // Find the diameter of the component starting at startNode
            componentDiameter := g.findComponentDiameter(startNode, visited)
            
            if componentDiameter > maxForestDiameter {
                maxForestDiameter = componentDiameter
            }
        }
    }
    
    return maxForestDiameter
}

// findComponentDiameter calculates the diameter of a single connected component
// starting from the source node and marks all nodes in the component as visited.
func (g DependencyGraph) findComponentDiameter(source int, visited map[int]bool) int {
    // 1. First, find all nodes in this component using a quick BFS/DFS for the component itself
    componentNodes := []int{source}
    queue := []int{source}
    visited[source] = true
    
    tempVisited := map[int]bool{source: true}
    
    // BFS to find all nodes in the component
    for len(queue) > 0 {
        u := queue[0]
        queue = queue[1:]
        
        for _, v := range g.Adj[u] {
            if !tempVisited[v] {
                tempVisited[v] = true
                visited[v] = true // Mark in the main map
                componentNodes = append(componentNodes, v)
                queue = append(queue, v)
            }
        }
    }

    // Handle single isolated node component
    if len(componentNodes) <= 1 {
        return 0
    }

    maxComponentDistance := 0
    
    // 2. Run BFS from every node in the component to find the maximum shortest path (diameter)
    for _, startNode := range componentNodes {
        // Run BFS, only considering nodes within this component
        distances := g.bfs(startNode)
        
        currentMaxDist := 0
        for _, dist := range distances {
            // Only consider distances to nodes within the current component
            if dist != math.MaxInt32 && currentMaxDist < dist {
                currentMaxDist = dist
            }
        }
        
        if currentMaxDist > maxComponentDistance {
            maxComponentDistance = currentMaxDist
        }
    }
    
    return maxComponentDistance
}

// bfs performs a Breadth-First Search from a source node
func (g DependencyGraph) bfs(source int) map[int]int {
    distances := make(map[int]int)
    queue := []int{source}
    
    for v := range g.Adj {
        distances[v] = math.MaxInt32
    }
    distances[source] = 0

    for len(queue) > 0 {
        u := queue[0]
        queue = queue[1:]
        
        for _, v := range g.Adj[u] {
            if distances[v] == math.MaxInt32 {
                distances[v] = distances[u] + 1
                queue = append(queue, v)
            }
        }
    }
    
    return distances
}

// FiniteCores adds edges to the graph based on the core dependency rule.
// An edge is added between i and j (undirected) whenever i + K <= j.
func (g DependencyGraph) FiniteCores(K int) {
    // K must be non-negative
    if K < 0 {
        fmt.Println("Warning: K must be non-negative for FiniteCores logic. No edges added.")
        return
    }

    // Get the highest vertex index
    maxVertex := -1
    for v := range g.Adj {
        if v > maxVertex {
            maxVertex = v
        }
    }

    // Since vertices start at 0 and go up to maxVertex
    // The total number of vertices N is maxVertex + 1
    N := maxVertex + 1
    if N <= K {
        // If there are too few nodes, the condition i + K <= j may never be met.
        // For example, if N=5 and K=5: max i is 4. 4 + 5 <= j is impossible since max j is 4.
        return
    }

    // Iterate through all unique pairs (i, j) where i < j
    for i := 0; i < N; i++ {
        for j := i + 1; j < N; j++ {
            // Apply the dependency rule: i + K <= j
            if i + K <= j {
                // Since the graph is undirected, we add the edge in both directions.
                
                // Add j to i's list (if not already present)
                if !contains(g.Adj[i], j) {
                    g.Adj[i] = append(g.Adj[i], j)
                    sort.Ints(g.Adj[i])
                }

                // Add i to j's list (if not already present)
                if !contains(g.Adj[j], i) {
                    g.Adj[j] = append(g.Adj[j], i)
                    sort.Ints(g.Adj[j])
                }
            }
        }
    }
}

// --- Placeholder/Previous Functions (Included for a Runnable Program) ---

//func (g DependencyGraph) AddEdge(u, v int) error { /* ... */ return nil }
//func (g DependencyGraph) RemoveEdge(u, v int) error { /* ... */ return nil }
//func (g DependencyGraph) Dependency(vertex int) ([]int, error) { /* ... */ return nil, nil }
//func contains(slice []int, item int) bool { /* ... */ return false }
//func removeElement(slice []int, val int) ([]int, bool) { /* ... */ return slice, false }
//func (g DependencyGraph) Display() { /* ... */ }

// NOTE: For brevity, the full implementations of the previous functions are 
// omitted here but would be included in the runnable Go file.
// I will ensure the main function is complete for testing the new logic.

//func main() {
//    // --- Full implementations of helper functions are required for a complete main ---
//    // (Pasting them here for a fully functional example)
//    // ... (AddEdge, RemoveEdge, Dependency, contains, removeElement, Display from previous response)
//    
//    // --- Test Case: Forest (Two components with different diameters) ---
//	n := 7
//    graph := NewDependencyGraph(n, 901)
//    
//    // Component 1 (Diameter 2): 0-1-2 (Path length 2)
//    graph.AddEdge(0, 1)
//    graph.AddEdge(1, 2)
//    
//    // Component 2 (Diameter 4): 3-4-5-6-7 (Path length 4)
//    graph.AddEdge(3, 4)
//    graph.AddEdge(4, 5)
//    graph.AddEdge(5, 6)
//    graph.AddEdge(6, 7) // Add 7 node if vertices are not restricted to 0..n-1
//    
//    // We must re-index to n=8 for the above nodes to exist 0..7
//    // Rerunning test with n=8 for proper vertex indexing
//    n = 8
//    graph = NewDependencyGraph(n, 901)
//    graph.AddEdge(0, 1)
//    graph.AddEdge(1, 2) // Component 1: Diameter 2
//    graph.AddEdge(3, 4)
//    graph.AddEdge(4, 5)
//    graph.AddEdge(5, 6)
//    graph.AddEdge(6, 7) // Component 2: Diameter 4
//    
//    // Isolated Node 7 is now used, isolated node is missing
//    
//	fmt.Printf("--- Test: Forest with Max Diameter ---\n")
//    graph.Display()
//    
//    // Expected result: Max path should be 4 (from component 2)
//    maxDiameter := graph.Diameter()
//	fmt.Printf("\nCalculated Maximum Component Diameter (MaxPath): %d\n", maxDiameter) // Expected: 4
//}

// The following helper functions must be included for the code to run correctly
func (g DependencyGraph) AddEdge(u, v int) error {
	if _, ok := g.Adj[u]; !ok { return fmt.Errorf("vertex %d does not exist in the graph", u) }
	if _, ok := g.Adj[v]; !ok { return fmt.Errorf("vertex %d does not exist in the graph", v) }
	if !contains(g.Adj[u], v) { g.Adj[u] = append(g.Adj[u], v); sort.Ints(g.Adj[u]) }
	if !contains(g.Adj[v], u) { g.Adj[v] = append(g.Adj[v], u); sort.Ints(g.Adj[v]) }
	return nil
}
func (g DependencyGraph) RemoveEdge(u, v int) error {
	if _, ok := g.Adj[u]; !ok { return fmt.Errorf("vertex %d does not exist in the graph", u) }
	if _, ok := g.Adj[v]; !ok { return fmt.Errorf("vertex %d does not exist in the graph", v) }
	g.Adj[u], _ = removeElement(g.Adj[u], v)
	g.Adj[v], _ = removeElement(g.Adj[v], u)
	return nil
}
func (g DependencyGraph) Dependency(vertex int) ([]int, error) {
	neighbors, ok := g.Adj[vertex]
	if !ok { return nil, fmt.Errorf("vertex %d does not exist in the graph", vertex) }
    result := make([]int, len(neighbors)); copy(result, neighbors)
	return result, nil
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
func (g DependencyGraph) Display() {
	fmt.Printf("Dependency Graph (BlockNo: %d)\n", g.BlockNo)
	fmt.Println("----------------------------------------")
	var vertices []int; for v := range g.Adj { vertices = append(vertices, v) }; sort.Ints(vertices)
	for _, v := range vertices { fmt.Printf("Vertex %d: %v\n", v, g.Adj[v]) }
}
