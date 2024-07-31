# DDV-DBS

# SystemVerilog Project

This repository contains various SystemVerilog tasks and their corresponding testbenches. The project uses ModelSim for compilation and simulation.

## Getting Started

### Prerequisites

Ensure you have ModelSim and GTKWave installed on your system. These tools are required for compiling, simulating, and viewing waveforms.

### Directory Structure

Each task is organized in its own folder. Inside each folder, you will find the SystemVerilog source files and the testbench file.

## Compilation and Simulation

Follow these steps to compile and simulate any task:

1. Open a terminal and navigate to the specific task folder.

    ```sh
    cd path/to/task_folder
    ```

2. Compile the SystemVerilog files using ModelSim.

    ```sh
    vlog -work work -sv *.sv
    ```

3. Run the simulation using the following command. Replace `testbench_file` with the actual name of the testbench file (without the `.sv` extension).

    ```sh
    vsim -c -do "run -all; quit" testbench_file
    ```

## Viewing Waveforms

After running the simulation, you can view the waveforms using GTKWave. The VCD file name is specified at the end of the `initial begin` block in each testbench file.

For example, in the `scoreboard` task, the VCD file name is `scoreboard.vcd`.

1. Open GTKWave and load the VCD file.

    ```sh
    gtkwave scoreboard.vcd
    ```

Replace `scoreboard.vcd` with the actual VCD file name for other tasks.

## Example

Here is an example workflow for the `scoreboard` task:

1. Navigate to the `scoreboard` folder:

    ```sh
    cd scoreboard
    ```

2. Compile the files:

    ```sh
    vlog -work work -sv *.sv
    ```

3. Run the simulation:

    ```sh
    vsim -c -do "run -all; quit" dut_tb
    ```

4. View the waveforms:

    ```sh
    gtkwave scoreboard.vcd
    ```

## License

This project is licensed under the MIT License.
