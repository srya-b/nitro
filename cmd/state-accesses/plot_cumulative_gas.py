#!/usr/bin/env python

import sys
import pandas as pd
import matplotlib.pyplot as plt

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
        create_cumulative_plot2(sys.argv[1], sys.argv[2])
        
    else:
        print("Usage:")
        print("  Plot:    python script.py <input_csv_file> <output_image_file>")
        print("  Compare: python script.py --compare <file1.csv> <file2.csv>")
        sys.exit(1)
