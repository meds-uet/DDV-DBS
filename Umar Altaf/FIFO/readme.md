Overview
This repository contains the implementation of a FIFO (First-In-First-Out) buffer in SystemVerilog. FIFO buffers are essential in digital systems for temporary data storage and synchronization between different clock domains.

Features
Parameterized width and depth.
Supports synchronous reset, write enable, and read enable signals.
Provides full and empty status flags.
Includes a testbench for functional verification.
Files
fifo.sv
This file contains the SystemVerilog code for the FIFO module. The module handles write and read operations, managing the data storage and providing status flags to indicate whether the FIFO is full or empty.

tb_fifo.sv
This file contains the SystemVerilog testbench for the FIFO module. The testbench simulates various write and read operations to verify the correct behavior of the FIFO.

Usage
Prerequisites
To simulate the FIFO module and its testbench, you need a SystemVerilog simulator such as ModelSim, VCS, or any other compatible tool.