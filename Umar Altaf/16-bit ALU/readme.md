
Overview
This repository contains the implementation of a 16-bit Arithmetic Logic Unit (ALU) in SystemVerilog. The ALU performs a variety of arithmetic and logic operations on 16-bit inputs, providing a versatile component for digital systems.

Features
Supports arithmetic operations: addition, subtraction.
Supports logic operations: Add, Sub,AND, XOR.
Handles 16-bit wide inputs and produces a 16-bit or 17-bit output.
Includes a testbench for functional verification.
Files
alu.sv
This file contains the SystemVerilog code for the 16-bit ALU module. The module takes two 16-bit inputs and a 3-bit operation code, producing a 17-bit output.

tb_alu.sv
This file contains the SystemVerilog testbench for the ALU module. The testbench applies various test vectors and verifies the ALU's output.

Usage
Prerequisites
To simulate the ALU module and its testbench, you need a SystemVerilog simulator such as ModelSim, VCS, or any other compatible tool.