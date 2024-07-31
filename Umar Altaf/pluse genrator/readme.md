Pulse Generator
Overview
This repository contains a SystemVerilog implementation of a pulse generator. The module generates an output pulse when the input transitions from 0 to 1. This is useful in various digital systems where detecting rising edges of signals is required.

Features
Detects rising edge transitions (0 to 1) on the input signal.
Generates a corresponding output pulse.
Includes a testbench for verifying the functionality of the pulse generator
Files
pulse_generator.sv
This file contains the SystemVerilog code for the pulse generator module. The module monitors the input signal and generates an output pulse on detecting a transition from 0 to 1.

tb_pulse_generator.sv
This file contains the SystemVerilog testbench for the pulse generator. The testbench verifies the functionality of the pulse generator by applying various test vectors and checking the output.
Usage
Prerequisites
To simulate the pulse generator module and its testbench, you need a SystemVerilog simulator such as ModelSim, VCS, or any other compatible tool.