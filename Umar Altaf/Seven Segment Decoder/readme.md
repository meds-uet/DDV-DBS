Overview
This repository contains the implementation of a 7-segment display decoder in SystemVerilog. The decoder converts a 4-bit binary input into the corresponding 7-segment display output, allowing the representation of hexadecimal digits (0-9, A-F).

Features
Converts 4-bit binary input to 7-segment display output.
Supports hexadecimal digits (0-9, A-F).
Includes a testbench for functional verification.

Files
seven_segment_decoder.sv
This file contains the SystemVerilog code for the 7-segment display decoder module. The module takes a 4-bit binary input and produces a 7-bit output corresponding to the segments of a 7-segment display.

tb_seven_segment_decoder.sv
This file contains the SystemVerilog testbench for the 7-segment display decoder. The testbench applies various test vectors and verifies the decoder's output.

Usage
Prerequisites
To simulate the 7-segment display decoder module and its testbench, you need a SystemVerilog simulator such as ModelSim, VCS, or any other compatible tool.