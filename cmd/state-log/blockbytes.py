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
    tick_interval = 5
    
    # Generate labels for all filtered bins
    labels = [f'[{b} - {b+bin_width-1}]' for b in filtered_bins]

    # Show only a subset of the ticks to avoid overcrowding the x-axis
    plt.xticks(filtered_bins[::tick_interval], labels[::tick_interval], rotation=45, ha='right')
    
    plt.tight_layout()
    
    # Save the plot to a file
    plt.savefig(save_path)
    print(f"Histogram saved as '{save_path}'")

def plot_float_histogram(file_path, save_path, bin_width):
    """
    Reads histogram data from a CSV file and plots it (for FLOAT64 data).
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
                # Reads as FLOAT
                bin_start = float(row[0])
                count = int(row[1])
                bins.append(bin_start)
                counts.append(count)
            except (ValueError, IndexError) as e:
                print(f"Error parsing row: {row}. Skipping. Error: {e}")
                continue

    if not bins:
        print("No float data found to plot.")
        return

    ## Determine bin width from the sorted bins. Assumes uniform bin width.
    #bin_width = 1.0 # Default bin width for floats
    #if len(bins) > 1:
    #    bins.sort()
    #    # Calculate bin width and round to avoid float arithmetic issues.
    #    bin_width = round(bins[1] - bins[0], 6)
    #print("Final bin width:", bin_width)
    # Create the plot
    plt.figure(figsize=(10, 6))
    plt.bar(bins, counts, width=bin_width, align='edge', color='lightcoral', edgecolor='darkred')

    plt.xlabel('Bin Range (Float64)')
    plt.ylabel('Frequency')
    plt.title('Histogram of Float64 Data')
    
    # Set the tick interval (show every 5th tick for typical float data density)
    tick_interval = 1
    
    # Generate labels for all bins (formatted to 2 decimal places for cleaner display)
    # Histograms typically use an exclusive upper bound, e.g., [1.00 - 2.00)
    labels = [f'[{b:.2f} - {b+bin_width:.2f})' for b in bins] 

    # Show only a subset of the ticks to avoid overcrowding the x-axis
    plt.xticks(bins[::tick_interval], labels[::tick_interval], rotation=45, ha='right')
    
    plt.tight_layout()
    
    # Save the plot to a file
    plt.savefig(save_path)
    print(f"Float64 Histogram saved as '{save_path}'")


import sys

if __name__ == "__main__":
    #allowed = {"block-histogram", "finite-cores-histogram", "infinite-cores-histogram", "finite-cores-speedup-histogram", "infinite-cores-speedup-histogram"}
    if len(sys.argv)-1 == 0:
        raise Exception("No filename included")
    #assert sys.argv[1] in allowed
    #file_to_read = "/home/admin/surya/nitro/block-histogram.csv"
    #file_to_save = "/home/admin/surya/nitro/block-histogram.png"
    file_to_read = "/home/admin/surya/nitro/{}.csv".format(sys.argv[1])
    file_to_save = "/home/admin/surya/nitro/{}.png".format(sys.argv[1])
    if "speedup" in sys.argv[1]:
        bin_width = float(sys.argv[2])
        plot_float_histogram(file_to_read, file_to_save, bin_width)
    else:
        plot_histogram(file_to_read, file_to_save)

