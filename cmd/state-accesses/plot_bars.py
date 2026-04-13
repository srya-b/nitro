import matplotlib.pyplot as plt
import matplotlib.ticker as ticker
import pandas as pd

# 1. Load the data
filename = '/home/admin/surya/slot-writes-Aug10.csv'

try:
    # Read the CSV with headers 'BinStart' and 'Count'
    df = pd.read_csv(filename, usecols=['BinStart', 'Count'])
    
    # Verify the columns exist
    #if 'BinStart' not in df.columns or 'Count' not in df.columns:
    #    print(f"Error: The file must contain columns 'BinStart' and 'Count'. Found: {list(df.columns)}")
    #    exit()
except ValueError as e:
    print(f"Error: the file must contain columns 'BinStart' and 'Count'.\nDetails: {e}")
    exit()
except FileNotFoundError:
    print(f"Error: The file '{filename}' was not found.")
    exit()

# 2. Filter the data
# Keep only rows where 'Count' is strictly greater than 10
df_filtered = df[df['Count'] > 100]

df_filtered = df_filtered.iloc[:100]

# Check if data remains after filtering
if df_filtered.empty:
    print("Warning: No data remaining after filtering for Count > 10.")
    exit()

# Prepare lists for plotting
x_values = df_filtered['BinStart']
y_values = df_filtered['Count']

# 3. Create the Line Graph
plt.figure(figsize=(10, 6))

# Plotting the filtered data
plt.plot(x_values, y_values, color='skyblue', marker='o', linestyle='-', linewidth=2, markerfacecolor='blue', markeredgecolor='blue', markersize=6)

# 4. Formatting

# Remove x-axis labels and ticks completely
plt.xticks([]) 

# Set y-axis ticks to be spaced by 100
ax = plt.gca()
ax.yaxis.set_major_locator(ticker.MultipleLocator(100000))

# Add a label to y-axis
plt.ylabel('Count')

# 5. Save the plot
output_file = '/home/admin/surya/slot-writes-chart-Aug10.png'
plt.savefig(output_file, dpi=300, bbox_inches='tight')

print(f"Chart saved successfully as {output_file}")
