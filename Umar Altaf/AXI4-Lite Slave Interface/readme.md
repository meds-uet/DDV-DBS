Overview
This repository contains the implementation of an AXI4-Lite Slave Interface in SystemVerilog. The AXI4-Lite protocol is a simplified version of the AXI4 protocol designed for communication with low-throughput peripherals in SoCs.

Features
Supports 32-bit address and data buses.
Implements read and write operations.
Handles AXI4-Lite valid, ready, and response signals.
Uses a state machine to manage read and write transactions.
Includes a testbench for functional verification.
Files
axi4_lite_slave.sv
This file contains the SystemVerilog code for the AXI4-Lite Slave Interface module. The module handles read and write requests from an AXI4-Lite master, managing the various signals and state transitions required by the protocol.

tb_axi4_lite_slave.sv
This file contains the SystemVerilog testbench for the AXI4-Lite Slave Interface module. The testbench simulates various read and write transactions to verify the correct behavior of the slave interface.

Usage
Prerequisites
To simulate the AXI4-Lite Slave Interface module and its testbench, you need a SystemVerilog simulator such as ModelSim, VCS, or any other compatible tool.