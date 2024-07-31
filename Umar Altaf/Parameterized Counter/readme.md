Overview
This repository contains the implementation of a parameterized counter in SystemVerilog. The counter module is versatile and can be configured to count up or down, reset synchronously, and generate an overflow signal when the counter wraps around.

Features
Parameterizable bit width.
Supports both up and down counting modes.
Synchronous reset functionality.
Overflow signal generation.
Includes a testbench for functional verification.
Files
p_counter.sv
This file contains the SystemVerilog code for the parameterized counter module. The module supports both up and down counting based on a parameter, a synchronous reset, and generates an overflow signal when the counter reaches its maximum value and wraps around.

tb_p_counter.sv
This file contains the SystemVerilog testbench for the counter module. The testbench simulates various counting operations to verify the correct behavior of the counter.

Usage
Prerequisites
To simulate the counter module and its testbench, you need a SystemVerilog simulator such as ModelSim, VCS, or any other compatible tool.