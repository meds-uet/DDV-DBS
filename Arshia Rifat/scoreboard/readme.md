This repository contains a SystemVerilog implementation of a FIFO (First-In-First-Out) module, an ALU (Arithmetic Logic Unit) reference model, and a comprehensive testbench environment for verification.

## Files

1. `fifo_scoreboard.svh`: FIFO module implementation
2. `ref_alu.sv`: ALU reference model
3. `scoreboard.sv`: Scoreboard class for result verification
4. `scoreboard_tb.sv`: Testbench for the FIFO and ALU modules

## Features

- Parameterized FIFO module with configurable data width and depth
- ALU reference model supporting various operations
- Comprehensive testbench environment including:
  - Clock generation
  - Reset sequence
  - ALU operation simulation
  - FIFO write and read operations
  - Scoreboard for result verification
- Multiple test cases covering different ALU operations

## Testbench Structure

The testbench (`scoreboard_tb.sv`) includes:
- DUT instantiation (FIFO)
- ALU reference model instantiation
- Scoreboard for result verification
- Test sequence with multiple operations:
- Addition
- Subtraction
- Bitwise AND

## Scoreboard

The scoreboard (`scoreboard.sv`) provides:
- Storage for expected results
- Comparison of actual outputs with expected results
- Tracking of correct and erroneous outputs
- Summary reporting of verification results

## Usage

To use this project:
1. You need to have a SystemVerilog compatible simulator installed
2. Compile the source files
3. Run the simulation using your simulator's command on testbench file `scoreboard_tb.sv`.