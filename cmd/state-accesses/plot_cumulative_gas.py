#!/usr/bin/env python

import sys
import pandas as pd
import matplotlib.pyplot as plt

def create_cumulative_plot4(input_csv_path, output_image_path):
    """
    Reads a CSV, normalizes BlockNumber to start at 1,
    calculates cumulative sums, and saves a plot.
    
    Features:
    - Draws a dot at the end of each line.
    - Writes the value of the last point in scientific notation (3 sig digits).
    - Text and dot match the line color.
    - Shifts text labels vertically to prevent overlap.
    """
    print(f"Generating plot (v3) from '{input_csv_path}' to '{output_image_path}'...")
    try:
        df = pd.read_csv(input_csv_path)
    except FileNotFoundError:
        print(f"Error: The file '{input_csv_path}' was not found.")
        sys.exit(1)
    except Exception as e:
        print(f"Error reading CSV: {e}")
        sys.exit(1)

    # REQUIRED COLUMNS
    required_cols = ['Cores', 'Concurrent', 'Sequential', 'BlockNumber']
    if not all(col in df.columns for col in required_cols):
        print(f"Error: Input CSV must contain {required_cols} columns.")
        sys.exit(1)

    # --- Robust BlockNumber Normalization ---
    min_block = df['BlockNumber'].min()
    df['plot_block'] = df['BlockNumber'] - min_block + 1

    # Sort by Cores and the new plot_block
    df = df.sort_values(by=['Cores', 'plot_block'])

    # --- Part 1: Concurrent Cumulative Sum (per Core) ---
    df['cumulative_concurrent'] = df.groupby('Cores')['Concurrent'].cumsum()

    # --- Part 2: Sequential Cumulative Sum (Global) ---
    df_seq_data = df.groupby('plot_block')['Sequential'].first()
    sequential_cumulative = df_seq_data.sort_index().cumsum()

    # --- Plotting ---
    fig, ax = plt.subplots(figsize=(12, 8))
    
    unique_cores = sorted(df['Cores'].unique())
    
    # Collect label data for post-processing overlap resolution
    # Structure: {'x': float, 'y': float, 'val': float, 'color': str}
    labels = []

    for core_value in unique_cores:
        group_data = df[df['Cores'] == core_value]
        
        if core_value == -1:
            label = "Infinite"
        else:
            label = f"{int(core_value)}"

        # Plot the line
        line, = ax.plot(
            group_data['plot_block'],
            group_data['cumulative_concurrent'],
            label=label
        )
        
        # Collect label info
        if not group_data.empty:
            last_x = group_data['plot_block'].iloc[-1]
            last_y = group_data['cumulative_concurrent'].iloc[-1]
            color = line.get_color()
            
            ax.plot(last_x, last_y, 'o', color=color)
            labels.append({'x': last_x, 'y': last_y, 'val': last_y, 'color': color})

    # Plot the 'Sequential' line
    line_seq, = ax.plot(
        sequential_cumulative.index,
        sequential_cumulative.values,
        label='Sequential',
        linestyle='--',
        color='black'
    )
    
    # Collect Sequential label info
    if not sequential_cumulative.empty:
        last_x = sequential_cumulative.index[-1]
        last_y = sequential_cumulative.values[-1]
        color = 'black'
        
        ax.plot(last_x, last_y, 'o', color=color)
        labels.append({'x': last_x, 'y': last_y, 'val': last_y, 'color': color})

    # --- Overlap Resolution ---
    if labels:
        # 1. Sort labels by Y coordinate
        labels.sort(key=lambda d: d['y'])
        
        # 2. Determine Minimum Vertical Distance (e.g., 3% of total Y range)
        all_ys = [d['y'] for d in labels]
        y_min, y_max = min(all_ys), max(all_ys)
        # Ensure min_dist is non-zero even if all points are identical
        min_dist = (y_max - y_min) * 0.03 if y_max != y_min else 1.0
        if min_dist == 0: min_dist = 1.0

        # 3. Identify Clusters of Overlapping Labels
        clusters = []
        if len(labels) > 0:
            current_cluster = [0] # Store indices into 'labels'
            for i in range(1, len(labels)):
                # If distance to previous is less than threshold, add to cluster
                if (labels[i]['y'] - labels[i-1]['y']) < min_dist:
                    current_cluster.append(i)
                else:
                    clusters.append(current_cluster)
                    current_cluster = [i]
            clusters.append(current_cluster)

        # 4. Calculate New Y Positions
        for cluster in clusters:
            # Calculate the center of gravity of the *original* positions
            avg_y = sum(labels[i]['y'] for i in cluster) / len(cluster)
            
            # Calculate the total height required for this stack
            total_height = (len(cluster) - 1) * min_dist
            
            # Determine starting Y (bottom of the stack) centered around avg_y
            start_y = avg_y - (total_height / 2)
            
            # Assign new text positions
            for i, label_idx in enumerate(cluster):
                labels[label_idx]['text_y'] = start_y + (i * min_dist)

        # 5. Draw Annotations
        # Calculate X offset (e.g., 1.5% of X range) to push text slightly right
        x_limit_max = df['plot_block'].max()
        x_offset = x_limit_max * 0.015
        
        for l in labels:
            ax.annotate(
                f"{l['val']:.2e}", 
                xy=(l['x'], l['y']),                # Arrow points to data point
                xytext=(l['x'] + x_offset, l['text_y']), # Text is at resolved position
                textcoords='data',                   # Use data coordinates for text pos
                color=l['color'], 
                fontsize=9, 
                fontweight='bold',
                ha='left', 
                va='center',
                # Draw a connecting line if text moved significantly
                arrowprops=dict(
                    arrowstyle="-", 
                    color=l['color'], 
                    lw=0.5,
                    shrinkA=2, 
                    shrinkB=2
                )
            )

    ax.set_xlabel("Block Number (Shifted to start at 1)")
    ax.set_ylabel("Cumulative Sum")
    ax.set_title("Cumulative Concurrent (by Cores) and Sequential")
    
    ax.legend()
    ax.grid(True, linestyle='--', alpha=0.6)
    fig.tight_layout()

    try:
        plt.savefig(output_image_path)
        print(f"Plot successfully saved to '{output_image_path}'")
    except Exception as e:
        print(f"Error saving plot: {e}")
        sys.exit(1)

def create_cumulative_plot3(input_csv_path, output_image_path):
    """
    Reads a CSV, normalizes BlockNumber to start at 1,
    calculates cumulative sums, and saves a plot.
    """
    print(f"Generating plot from '{input_csv_path}' to '{output_image_path}'...")
    try:
        df = pd.read_csv(input_csv_path)
    except FileNotFoundError:
        print(f"Error: The file '{input_csv_path}' was not found.")
        sys.exit(1)
    except Exception as e:
        print(f"Error reading CSV: {e}")
        sys.exit(1)

    # REQUIRED COLUMNS
    required_cols = ['Cores', 'Concurrent', 'Sequential', 'BlockNumber']
    if not all(col in df.columns for col in required_cols):
        print(f"Error: Input CSV must contain {required_cols} columns.")
        sys.exit(1)

    # --- Robust BlockNumber Normalization ---
    # Shift BlockNumber so the sequence starts strictly at 1.
    # This handles cases where BlockNumber is 0-based, 1-based, or huge (e.g., 365580454).
    min_block = df['BlockNumber'].min()
    df['plot_block'] = df['BlockNumber'] - min_block + 1

    # Sort by Cores and the new plot_block to ensure correct line drawing order
    df = df.sort_values(by=['Cores', 'plot_block'])

    # --- Part 1: Concurrent Cumulative Sum (per Core) ---
    df['cumulative_concurrent'] = df.groupby('Cores')['Concurrent'].cumsum()

    # --- Part 2: Sequential Cumulative Sum (Global) ---
    # Group by the plotting block number.
    # Since 'Sequential' is the same for all Cores in a block, we take the first one.
    df_seq_data = df.groupby('plot_block')['Sequential'].first()
    sequential_cumulative = df_seq_data.sort_index().cumsum()

    # --- Plotting ---
    fig, ax = plt.subplots(figsize=(12, 8))
    
    # Get unique cores (sorted numerically)
    unique_cores = sorted(df['Cores'].unique())

    # Store final values for annotation: list of (value, label)
    final_values = []

    for core_value in unique_cores:
        group_data = df[df['Cores'] == core_value]
        
        if core_value == -1:
            label = "Infinite"
        else:
            label = f"{int(core_value)}"

        ax.plot(
            group_data['plot_block'],
            group_data['cumulative_concurrent'],
            label=label
        )
        
        # Capture final value for difference calculation
        if not group_data.empty:
            last_val = group_data['cumulative_concurrent'].iloc[-1]
            final_values.append((last_val, label))
    
    # Plot the 'Sequential' line
    ax.plot(
        sequential_cumulative.index,
        sequential_cumulative.values,
        label='Sequential',
        linestyle='--',
        color='black'
    )
    # Capture Sequential final value
    if not sequential_cumulative.empty:
        last_seq_val = sequential_cumulative.iloc[-1]
        final_values.append((last_seq_val, 'Sequential'))

    # --- Annotate Differences ---
    # Sort by value (lowest to highest)
    final_values.sort(key=lambda x: x[0])
    
    x_max = df['plot_block'].max()
    # Define brace width as 2% of the total x range
    brace_w = x_max * 0.02
    
    # Iterate and annotate differences with the curve below
    # We skip index 0 because there is no curve below the lowest one
    for i in range(1, len(final_values)):
        current_val, _ = final_values[i]
        prev_val, _ = final_values[i-1]
        diff = current_val - prev_val
        mid_val = (current_val + prev_val) / 2
        
        # Draw the brace (Square bracket with a pointer)
        # 1. Main Bracket Body
        ax.plot(
            [x_max, x_max + brace_w, x_max + brace_w, x_max],
            [current_val, current_val, prev_val, prev_val],
            color='black', lw=1
        )
        
        # 2. Pointer Tick
        ax.plot(
            [x_max + brace_w, x_max + brace_w * 1.5],
            [mid_val, mid_val],
            color='black', lw=1
        )

        # 3. Add text
        annotation_text = f"+{diff:.3e}"
        ax.text(
            x_max + brace_w * 1.6, 
            mid_val, 
            annotation_text, 
            va='center', 
            ha='left',
            fontsize=8,
            color='black'
        )

    ax.set_xlabel("Block Number (Shifted to start at 1)")
    ax.set_ylabel("Cumulative Sum")
    ax.set_title("Cumulative Concurrent (by Cores) and Sequential")
    
    # Add legend
    ax.legend()
    
    # Add grid
    ax.grid(True, linestyle='--', alpha=0.6)
    
    # Ensure layout is tight
    fig.tight_layout()

    try:
        plt.savefig(output_image_path)
        print(f"Plot successfully saved to '{output_image_path}'")
    except Exception as e:
        print(f"Error saving plot: {e}")
        sys.exit(1)


def create_cumulative_plot2(input_csv_path, output_image_path):
    """
    Reads a CSV, normalizes BlockNumber to start at 1,
    calculates cumulative sums, and saves a plot.
    """
    print(f"Generating plot from '{input_csv_path}' to '{output_image_path}'...")
    try:
        df = pd.read_csv(input_csv_path)
    except FileNotFoundError:
        print(f"Error: The file '{input_csv_path}' was not found.")
        sys.exit(1)
    except Exception as e:
        print(f"Error reading CSV: {e}")
        sys.exit(1)

    # REQUIRED COLUMNS
    required_cols = ['Cores', 'Concurrent', 'Sequential', 'BlockNumber']
    if not all(col in df.columns for col in required_cols):
        print(f"Error: Input CSV must contain {required_cols} columns.")
        sys.exit(1)

    # --- Robust BlockNumber Normalization ---
    # Shift BlockNumber so the sequence starts strictly at 1.
    # This handles cases where BlockNumber is 0-based, 1-based, or huge (e.g., 365580454).
    min_block = df['BlockNumber'].min()
    df['plot_block'] = df['BlockNumber'] - min_block + 1

    # Sort by Cores and the new plot_block to ensure correct line drawing order
    df = df.sort_values(by=['Cores', 'plot_block'])

    # --- Part 1: Concurrent Cumulative Sum (per Core) ---
    df['cumulative_concurrent'] = df.groupby('Cores')['Concurrent'].cumsum()

    # --- Part 2: Sequential Cumulative Sum (Global) ---
    # Group by the plotting block number.
    # Since 'Sequential' is the same for all Cores in a block, we take the first one.
    df_seq_data = df.groupby('plot_block')['Sequential'].first()
    sequential_cumulative = df_seq_data.sort_index().cumsum()

    # --- Plotting ---
    fig, ax = plt.subplots(figsize=(12, 8))
    
    # Get unique cores (sorted numerically)
    unique_cores = sorted(df['Cores'].unique())

    for core_value in unique_cores:
        group_data = df[df['Cores'] == core_value]
        
        if core_value == -1:
            label = "Infinite"
        else:
            label = f"{int(core_value)}"

        ax.plot(
            group_data['plot_block'],
            group_data['cumulative_concurrent'],
            label=label
        )
    
    # Plot the 'Sequential' line
    ax.plot(
        sequential_cumulative.index,
        sequential_cumulative.values,
        label='Sequential',
        linestyle='--',
        color='black'
    )

    ax.set_xlabel("Block Number (Shifted to start at 1)")
    ax.set_ylabel("Cumulative Sum")
    ax.set_title("Cumulative Concurrent (by Cores) and Sequential")
    
    # Add legend
    ax.legend()
    
    # Add grid
    ax.grid(True, linestyle='--', alpha=0.6)
    
    # Ensure layout is tight
    fig.tight_layout()

    try:
        plt.savefig(output_image_path)
        print(f"Plot successfully saved to '{output_image_path}'")
    except Exception as e:
        print(f"Error saving plot: {e}")
        sys.exit(1)

def create_cumulative_plot(input_csv_path, output_image_path):
    """
    Reads a CSV, calculates cumulative 'Concurrent' sums grouped by 'Cores',
    calculates a separate cumulative 'Sequential' sum, and saves a plot.
    """
    try:
        # Read the CSV file
        df = pd.read_csv(input_csv_path)
    except FileNotFoundError:
        print(f"Error: The file '{input_csv_path}' was not found.")
        sys.exit(1)
    except Exception as e:
        print(f"Error reading CSV: {e}")
        sys.exit(1)

    # Ensure required columns exist
    required_cols = ['Cores', 'Concurrent', 'Sequential']
    if not all(col in df.columns for col in required_cols):
        print(f"Error: Input CSV must contain {required_cols} columns.")
        sys.exit(1)

    # Sort by 'Cores' to ensure a consistent plotting order
    # Assuming data within each 'Cores' group is already in the correct "block" order
    df = df.sort_values(by='Cores')

    # --- Part 1: Calculate 'Concurrent' cumulative sums (per Core) ---
    
    # Calculate the cumulative sum and 1-based block number within each group
    df['cumulative_concurrent'] = df.groupby('Cores')['Concurrent'].cumsum()
    df['block_number'] = df.groupby('Cores').cumcount() + 1

    # --- Part 2: Calculate 'Sequential' cumulative sum (per block) ---
    
    # Get the unique Sequential value for each block number.
    # We use .first() based on the assumption that all 'Sequential' values
    # for a given block number are the same.
    df_seq_data = df.groupby('block_number')['Sequential'].first()
    
    # Sort by block_number (which is the index) just in case,
    # then calculate the cumulative sum.
    sequential_cumulative = df_seq_data.sort_index().cumsum()

    # --- Part 3: Plotting ---
    fig, ax = plt.subplots(figsize=(12, 8))

    # Get unique core values to iterate over
    unique_cores = df['Cores'].unique()

    # Plot the 'Concurrent' lines
    for core_value in unique_cores:
        # Get the data for this specific core
        group_data = df[df['Cores'] == core_value]

        # Determine the label
        if core_value == -1:
            label = "Infinite"
        else:
            label = f"{int(core_value)}" # Use int to avoid .0

        # Plot the line for this group
        ax.plot(
            group_data['block_number'],
            group_data['cumulative_concurrent'],
            label=label
        )
    
    # Plot the 'Sequential' line
    ax.plot(
        sequential_cumulative.index,   # x-axis (block_number)
        sequential_cumulative.values,  # y-axis (cumulative_sequential)
        label='Sequential',
        linestyle='--',               # Make it dashed
        color='black'                  # Make it black
    )

    # --- Add plot enhancements ---
    ax.set_xlabel("Block Number")
    ax.set_ylabel("Cumulative Sum")
    ax.set_title("Cumulative Concurrent (by Cores) and Sequential")
    
    # Add a legend
    ax.legend()
    
    # Add grid for readability
    ax.grid(True, linestyle='--', alpha=0.6)
    
    # Ensure layout is tight
    fig.tight_layout()

    # Save the figure to the specified output file
    try:
        plt.savefig(output_image_path)
        print(f"Plot successfully saved to '{output_image_path}'")
    except Exception as e:
        print(f"Error saving plot: {e}")
        sys.exit(1)

def compare_csvs(csv1_path, csv2_path):
    """
    Compares two CSVs to ensure that for every combination of BlockNumber 
    and Cores, the values in Sequential and Concurrent are the same.
    """
    print(f"Comparing '{csv1_path}' and '{csv2_path}'...")
    
    try:
        df1 = pd.read_csv(csv1_path)
        df2 = pd.read_csv(csv2_path)
    except FileNotFoundError as e:
        print(f"Error: {e}")
        sys.exit(1)

    required_cols = {'Cores', 'Concurrent', 'Sequential', 'BlockNumber'}

    # Pre-process both dataframes
    for i, df in enumerate([df1, df2], 1):
        # Check columns
        if not required_cols.issubset(df.columns):
            print(f"Error: File {i} is missing required columns: {required_cols}")
            sys.exit(1)
        
        # Set index for exact alignment based on Cores AND BlockNumber
        # Verify duplicates to prevent merge errors
        if df.duplicated(subset=['Cores', 'BlockNumber']).any():
            print(f"Error: File {i} has duplicate entries for the same Cores/BlockNumber combination.")
            sys.exit(1)
            
        df.set_index(['Cores', 'BlockNumber'], inplace=True)

    # Align dataframes on the index
    merged = df1.join(df2, lsuffix='_1', rsuffix='_2', how='outer')

    # 1. Check for missing rows (Structural mismatch)
    if merged.isnull().any().any():
        print("FAILURE: Files have different rows (missing Cores or BlockNumbers in one file).")
        # Show rows where one side is null
        print(merged[merged.isnull().any(axis=1)])
        sys.exit(1)

    # 2. Compare values
    concurrent_diff = merged[merged['Concurrent_1'] != merged['Concurrent_2']]
    sequential_diff = merged[merged['Sequential_1'] != merged['Sequential_2']]

    if concurrent_diff.empty and sequential_diff.empty:
        print("SUCCESS: Files match perfectly.")
    else:
        print("FAILURE: Differences found.")
        
        if not concurrent_diff.empty:
            print(f"\nFound {len(concurrent_diff)} mismatches in 'Concurrent':")
            print(concurrent_diff[['Concurrent_1', 'Concurrent_2']].head())
        
        if not sequential_diff.empty:
            print(f"\nFound {len(sequential_diff)} mismatches in 'Sequential':")
            print(sequential_diff[['Sequential_1', 'Sequential_2']].head())
        sys.exit(1)

if __name__ == "__main__":
# Check if user wants to compare
    if len(sys.argv) > 1 and sys.argv[1] == '--compare':
        if len(sys.argv) != 4:
            print("Usage for comparison: python script.py --compare <file1.csv> <file2.csv>")
            sys.exit(1)
        compare_csvs(sys.argv[2], sys.argv[3])
    
    # Standard plotting mode
    elif len(sys.argv) == 3:
        create_cumulative_plot4(sys.argv[1], sys.argv[2])
        
    else:
        print("Usage:")
        print("  Plot:    python script.py <input_csv_file> <output_image_file>")
        print("  Compare: python script.py --compare <file1.csv> <file2.csv>")
        sys.exit(1)
