import csv
import matplotlib.pyplot as plt

def plot_histogram(file_path, save_path):
    """
    Reads histogram data from a CSV file and plots it.
    The plot is saved to the specified save_path.
    """
    bins = []
    counts = []
    
    with open(file_path, 'r', newline='') as csvfile:
        reader = csv.reader(csvfile)
        # Skip the header row
        try:
            next(reader) 
        except StopIteration:
            print("The CSV file is empty or has no header.")
            return

        for row in reader:
            try:
                # Assuming the first column is the bin start and the second is the count.
                bin_start = int(row[0])
                count = int(row[1])
                bins.append(bin_start)
                counts.append(count)
            except (ValueError, IndexError) as e:
                print(f"Error parsing row: {row}. Skipping. Error: {e}")
                continue

    if not bins:
        print("No data found to plot.")
        return

    # Filter out bins at or above 1,000,000
    filtered_bins = []
    filtered_counts = []
    for i in range(len(bins)):
        if bins[i] < 1000000:
            filtered_bins.append(bins[i])
            filtered_counts.append(counts[i])

    # If the filtered data is empty, there's nothing to plot.
    if not filtered_bins:
        print("No data found to plot after filtering.")
        return

    # Determine bin width from the sorted bins. Assumes uniform bin width.
    bin_width = 10000
    if len(filtered_bins) > 1:
        filtered_bins.sort()
        bin_width = filtered_bins[1] - filtered_bins[0]

    # Create the plot
    plt.figure(figsize=(10, 6))
    plt.bar(filtered_bins, filtered_counts, width=bin_width, align='edge', color='skyblue', edgecolor='blue')

    plt.xlabel('Bin Range')
    plt.ylabel('Frequency')
    plt.title('Histogram of Data')
    
    # Set the tick interval to show every 10th tick on the x-axis
    tick_interval = 10
    
    # Generate labels for all filtered bins
    labels = [f'[{b} - {b+bin_width-1}]' for b in filtered_bins]

    # Show only a subset of the ticks to avoid overcrowding the x-axis
    plt.xticks(filtered_bins[::tick_interval], labels[::tick_interval], rotation=45, ha='right')
    
    plt.tight_layout()
    
    # Save the plot to a file
    plt.savefig(save_path)
    print(f"Histogram saved as '{save_path}'")

if __name__ == "__main__":
    file_to_read = "histogram.csv"
    file_to_save = "histogram.png"
    plot_histogram(file_to_read, file_to_save)

