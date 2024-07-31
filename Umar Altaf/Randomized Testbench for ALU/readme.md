Overview
This repository contains the implementation and testbench of a 16-bit ALU (Arithmetic Logic Unit) in SystemVerilog, with randomized testing for verification. The ALU supports various operations such as addition, subtraction, bitwise AND, OR, and XOR. The testbench uses random inputs to thoroughly verify the functionality of the ALU.

Features
16-bit wide data paths.
Supports multiple arithmetic and logical operations.
Testbench with randomized input generation.
Assertions to verify correct functionality.
Files
R_ALU.sv
This file contains the SystemVerilog code for the ALU module. The ALU performs various arithmetic and logical operations based on a control signal.

tb_R_ALU.sv
This file contains the SystemVerilog testbench for the ALU module. The testbench uses randomized input values and control signals to test the ALU and includes assertions to check the correctness of the output.

Usage
Prerequisites
To simulate the ALU module and its testbench, you need a SystemVerilog simulator such as ModelSim, VCS, or any other compatible tool.