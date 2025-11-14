package main

func splitSliceIntoNParts[T any](slice []T, n int) [][]T {
	if n <= 0 {
		panic("Number of parts (n) must be greater than 0")
	}
	if len(slice) == 0 {
		return [][]T{}
	}

	// Calculate the base size of each part and the number of parts that will have an extra element
	basePartSize := len(slice) / n
	remainder := len(slice) % n

	var result [][]T
	start := 0

	for i := 0; i < n; i++ {
		end := start + basePartSize
		if i < remainder { // Distribute the remainder elements one by one
			end++
		}

		if start < len(slice) { // Ensure we don't try to slice beyond the original slice's bounds
			result = append(result, slice[start:end])
		} else {
			// If we've exhausted the original slice, add empty slices for the remaining parts
			result = append(result, []T{})
		}
		start = end
	}
	return result
}
