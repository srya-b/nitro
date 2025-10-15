import csv
import matplotlib.pyplot as plt
import sys
import os # Added for path manipulation

# --- Integer Histogram Plotting (Bar Chart) ---

def plot_histogram(file_path, save_path):
    """
    Reads histogram data from a CSV file and plots it (for INT data) as a bar chart.
    The plot is saved to the specified save_path.
    """
    bins = []
    counts = []
    
    try:
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
                    # Reads as INT
                    bin_start = int(row[0])
                    count = int(row[1])
                    bins.append(bin_start)
                    counts.append(count)
                except (ValueError, IndexError) as e:
                    print(f"Error parsing row: {row}. Skipping. Error: {e}")
                    continue
    except FileNotFoundError:
        print(f"Error: Input file not found: {file_path}")
        return

    if not bins:
        print("No data found to plot.")
        return

    # Filter out bins at or above 1,000,000 as requested
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

    plt.xlabel('Bin Range (Integers)')
    plt.ylabel('Frequency')
    plt.title('Histogram of Integer Data (Bar Chart)')
    
    # Set the tick interval to show every 10th tick on the x-axis
    tick_interval = 10
    
    # Generate labels for all filtered bins (using -1 for inclusive integer range)
    labels = [f'[{b} - {b+bin_width-1}]' for b in filtered_bins]

    # Show only a subset of the ticks to avoid overcrowding the x-axis
    plt.xticks(filtered_bins[::tick_interval], labels[::tick_interval], rotation=45, ha='right')
    
    plt.tight_layout()
    
    # Save the plot to a file
    plt.savefig(save_path)
    print(f"Integer Histogram (Bar Chart) saved as '{save_path}'")


# --- Float64 Histogram Plotting (Bar Chart) ---

def plot_float_histogram(file_path, save_path, bin_width):
    """
    Reads histogram data from a CSV file and plots it (for FLOAT64 data) as a bar chart.
    Accepts bin_width as an explicit parameter.
    The plot is saved to the specified save_path.
    """
    bins = []
    counts = []
    
    try:
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
    except FileNotFoundError:
        print(f"Error: Input file not found: {file_path}")
        return

    if not bins:
        print("No float data found to plot.")
        return

    # bin_width is now passed as a parameter and used directly
    
    # Create the plot
    plt.figure(figsize=(10, 6))
    plt.bar(bins, counts, width=bin_width, align='edge', color='lightcoral', edgecolor='darkred')

    plt.xlabel('Bin Range (Float64)')
    plt.ylabel('Frequency')
    plt.title('Histogram of Float64 Data (Bar Chart)')
    
    # Set the tick interval (show every 5th tick for typical float data density)
    tick_interval = 5
    
    # Generate labels for all bins (formatted to 2 decimal places for cleaner display)
    # Histograms typically use an exclusive upper bound, e.g., [1.00 - 2.00)
    labels = [f'[{b:.2f} - {b+bin_width:.2f})' for b in bins] 

    # Show only a subset of the ticks to avoid overcrowding the x-axis
    plt.xticks(bins[::tick_interval], labels[::tick_interval], rotation=45, ha='right')
    
    plt.tight_layout()
    
    # Save the plot to a file
    plt.savefig(save_path)
    print(f"Float64 Histogram (Bar Chart) saved as '{save_path}'")


# --- Multiple Line Histogram Plotting (Line Chart) ---

def plot_multiple_line_histogram(base_filenames, save_path, data_type, bin_width):
    """
    Reads histogram data from multiple CSV files, plots them as line graphs 
    on a single chart, and saves the plot to the specified save_path.
    """
    plt.figure(figsize=(12, 7))
    
    # Use different tick intervals based on data type for cleaner look
    tick_interval = 5 if data_type == float else 10
    
    # Variables to hold the last processed data for setting ticks/labels
    last_bins = []
    labels = []
    
    x_label = 'Bin Range (Float64)' if data_type == float else 'Bin Range (Integers)'
    title_suffix = f'Float64 Data (Bin Width: {bin_width})' if data_type == float else 'Integer Data'

    for fn in base_filenames:
        file_path = f"/home/admin/surya/nitro/from_file_100000/{fn}.csv"
        bins = []
        counts = []
        
        try:
            with open(file_path, 'r', newline='') as csvfile:
                reader = csv.reader(csvfile)
                next(reader) # Skip header
                
                for row in reader:
                    try:
                        bin_start = data_type(row[0]) # Use the determined data_type
                        count = int(row[1])
                        bins.append(bin_start)
                        counts.append(count)
                    except (ValueError, IndexError) as e:
                        print(f"Error parsing row in {file_path}: {row}. Skipping. Error: {e}")
                        continue
        except FileNotFoundError:
            print(f"Error: Input file not found: {file_path}. Skipping.")
            continue
        except StopIteration:
            print(f"The CSV file {file_path} is empty or has no header. Skipping.")
            continue

        if not bins:
            print(f"No data found to plot in {file_path}. Skipping.")
            continue

        current_bins = bins
        current_counts = counts
        
        # --- Type-Specific Filtering/Labeling ---
        if data_type == int:
            # Apply the integer data filter (only bins < 1000000)
            filtered_bins = []
            filtered_counts = []
            for i in range(len(bins)):
                if bins[i] < 1000000:
                    filtered_bins.append(bins[i])
                    filtered_counts.append(counts[i])
            
            if not filtered_bins:
                print(f"No data found in {file_path} after integer filtering. Skipping.")
                continue

            current_bins = filtered_bins
            current_counts = filtered_counts
            
            # Generate labels for x-axis (Int data uses inclusive labels)
            labels = [f'[{b} - {b+bin_width-1}]' for b in current_bins]
        else: # float data
            # Generate labels for x-axis (Float data uses exclusive upper bounds)
            labels = [f'[{b:.2f} - {b+bin_width:.2f})' for b in current_bins] 
        
        # Plot the current dataset as a line graph
        # os.path.splitext(fn)[0] is used to strip the potential file extension from the label
        plt.plot(current_bins, current_counts, marker='o', linestyle='-', label=os.path.basename(fn), linewidth=1.5)
        
        # Store the bins from the last successful plot for setting final ticks
        last_bins = current_bins
    
    if not last_bins:
        print("No valid data was plotted.")
        return

    # --- Final Plot Customization ---
    plt.xlabel(x_label)
    plt.ylabel('Frequency')
    plt.title(f'Multiple Histogram Overlays ({title_suffix})')
    
    # Set x-ticks based on the last dataset's bins and the generated labels
    if len(labels) > 20: # Heuristic to prevent tick overcrowding
         plt.xticks(last_bins[::tick_interval], labels[::tick_interval], rotation=45, ha='right')
    else:
         plt.xticks(last_bins, labels, rotation=45, ha='right')
        
    plt.legend(title="Data Series")
    plt.grid(True, linestyle='--', alpha=0.6)
    plt.tight_layout()
    
    # Save the plot to a file
    plt.savefig(save_path)
    print(f"Multiple Line Histogram saved as '{save_path}'")


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage (Single File): python plot_histogram.py <base_filename> [bin_width_float_only]")
        print("Usage (Multiple Lines): python plot_histogram.py multiple-line <output_filename.png> <fn1> <fn2> ... [bin_width_float_only]")
        print("Example 1 (Integer): python plot_histogram.py data")
        print("Example 2 (Float): python plot_histogram.py speedup_test 0.5")
        print("Example 3 (Multiple Int): python plot_histogram.py multiple-line my_int_plot.png data1 data2")
        print("Example 4 (Multiple Float): python plot_histogram.py multiple-line my_float_plot.png speedup1 speedup2 0.1")
        sys.exit(1)
        
    mode = sys.argv[1]

    if mode == "multiple-line":
        # Check minimum arguments: 4 (script, mode, save_path, fn1)
        if len(sys.argv) < 4:
            raise ValueError("In 'multiple-line' mode, you must provide an output filename and at least one input filename.")

        # 1. Extract the output file path
        save_path = '/home/admin/surya/nitro/' + sys.argv[2]
        
        # 2. Arguments containing filenames and optional bin_width start from sys.argv[3]
        input_args = sys.argv[3:]
        
        # Test if the last argument is a valid float (potential bin width)
        is_last_arg_float = False
        try:
            float(input_args[-1])
            is_last_arg_float = True
        except (ValueError, IndexError):
            pass

        # Determine which arguments are potential filenames
        if is_last_arg_float:
            potential_filenames = input_args[:-1] # Exclude the last arg (the float bin width)
        else:
            potential_filenames = input_args # All args are filenames

        if not potential_filenames:
            raise ValueError("No input filenames provided.")

        # Check for 'speedup' consistency
        has_speedup_list = ["speedup" in arg for arg in potential_filenames]
        
        all_float_mode = all(has_speedup_list)
        all_int_mode = not any(has_speedup_list) 

        if not (all_float_mode or all_int_mode):
            raise ValueError("In 'multiple-line' mode, all input filenames must either contain 'speedup' (float data) or none of them must (integer data). Mixed types are not supported.")

        if all_float_mode:
            # Must have a float bin_width argument (which is the last one)
            if not is_last_arg_float:
                 raise ValueError("Float 'multiple-line' mode (with 'speedup' in filenames) requires a float bin width argument as the last parameter.")

            # Assign bin_width and filenames
            bin_width = float(input_args[-1])
            filenames = input_args[:-1] # All but the last one are filenames
            data_type = float
            
        else: # all_int_mode
            # Ensure no extra argument was passed (only filenames)
            if is_last_arg_float:
                 raise ValueError("Integer 'multiple-line' mode does not accept a final numeric bin width argument. Only filenames are allowed.")
            
            bin_width = 10000 # Default int bin width
            filenames = input_args # All arguments are filenames
            data_type = int
            
        
        # Call with the new save_path
        plot_multiple_line_histogram(filenames, save_path, data_type, bin_width)

    else:
        # Existing single-file logic
        base_filename = mode
        
        # Define the input and output file paths based on the argument
        file_to_read = f"/home/admin/surya/nitro/{base_filename}.csv"
        file_to_save = f"/home/admin/surya/nitro/{base_filename}.png"

        # Check if the string "speedup" is in the base filename
        if "speedup" in base_filename:
            # If "speedup" is present, it requires an additional bin_width argument
            if len(sys.argv) != 3:
                print(f"Error: Float plotting (with 'speedup' in filename) requires a bin_width argument.")
                print(f"Usage: python plot_histogram.py {base_filename} <bin_width_float>")
                sys.exit(1)
            
            try:
                float_bin_width = float(sys.argv[2])
            except ValueError:
                print(f"Error: The provided bin width '{sys.argv[2]}' is not a valid float.")
                sys.exit(1)

            # Call the float plotting function with the specified bin width
            plot_float_histogram(file_to_read, file_to_save, float_bin_width)
        else:
            # Integer data - requires only 1 argument (base_filename)
            if len(sys.argv) != 2:
                print(f"Error: Integer plotting (without 'speedup' in filename) accepts only one argument: <base_filename>")
                sys.exit(1)
                
            # Call the integer plotting function
            plot_histogram(file_to_read, file_to_save)

