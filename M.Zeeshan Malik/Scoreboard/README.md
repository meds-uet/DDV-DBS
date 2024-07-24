# Scoreboard Module

The Scoreboard module in SystemVerilog provides functionality to verify the outputs of an Arithmetic Logic Unit (ALU) against expected results. It tracks match and mismatch counts and can report statistics at the end of simulation.

## Overview

The Scoreboard module includes the following features:
- Tracks expected results using a queue.
- Compares actual results with expected results.
- Counts the number of matches and mismatches.
- Reports statistics including match count, mismatch count, and the number of items left in the queue.

## Module Details

### Parameters
- `DATA_WIDTH`: Parameter specifying the width of the data (default: 8 bits).

### Internal Data Structures
- `expected_queue`: Queue to store expected results.
- `match_count`: Counter for the number of matches.
- `mismatch_count`: Counter for the number of mismatches.

### Methods

- `new()`: Constructor initializes match_count and mismatch_count.
- `add_expected(bit [DATA_WIDTH-1:0] expected)`: Adds an expected result to the queue.
- `compare_result(bit [DATA_WIDTH-1:0] actual)`: Compares the actual result with the expected result from the front of the queue.
- `report_statistics()`: Displays statistics including matches, mismatches, and the remaining items in the queue.

## Getting Started

These instructions will help you set up the project, simulate the Scoreboard module in Vivado, and understand the testbench.

### Prerequisites

Ensure you have the following installed:
- Vivado Design Suite

### Simulation Steps in Vivado

1. **Open Vivado:**
   - Launch Vivado Design Suite from your installed applications.

2. **Create a New Project:**

   - Click on `Create New Project`.
   - Follow the wizard to create an RTL project. Do not specify sources at this point.

3. **Add Sources:**

   - Go to `File -> Add Sources`.
   - Select `Add or Create Simulation Sources`.
   - Add `src/tb_scoreboard.sv` and `src/scoreboard.sv`.

4. **Set the Top Module:**

   - In the `Sources` window, right-click on `tb_scoreboard` and select `Set as Top`.

5. **Run Simulation:**

   - Go to the `Flow Navigator` pane.
   - Click on `Run Simulation` and then `Run Behavioral Simulation`.

### Testbench Overview

The testbench (`tb_scoreboard.sv`) includes the following test cases:
1. Adding expected results to the scoreboard.
2. Comparing actual results with expected results.
3. Reporting statistics including matches, mismatches, and remaining items in the queue.

Each test case demonstrates the functionality of the Scoreboard module in verifying the outputs of an ALU or similar component.



