This repository implements a Level to Pulse Converter in SystemVerilog, along with a comprehensive testbench including assertions for verification.

## Project Structure

- `LEVELTOPULSE.svh`: Main module implementing the Level to Pulse Converter
- `tb_LEVEL_TO_PULSE_Assertion.svh`: Testbench for the Level to Pulse Converter, including assertions

## Level to Pulse Converter

The Level to Pulse Converter is a digital circuit that converts a level signal into a single-cycle pulse. It's implemented as a Finite State Machine (FSM) with three states:
- S0: Idle state
- S1: Pulse detect state
- S2: Pulse generation state

### Features

- Synchronous reset
- Single-cycle pulse output
- Parameterized design for easy integration

## Testbench

The testbench provides a comprehensive verification environment for the Level to Pulse Converter. It includes:
- Clock generation
- Reset sequence
- Stimulus generation using a driver task
- Output monitoring
- Assertion-based verification

### Key Components

1. **Driver Task**: `apply_pulse` applies input pulses of varying widths
2. **Monitor Task**: Checks the output for correct pulse generation
3. **Assertion**: Verifies the pulse generation property

## Usage

To run the simulation:
1. You need to have a SystemVerilog compatible simulator installed
2. Compile both `LEVELTOPULSE.svh` and `tb_LEVEL_TO_PULSE_Assertion.svh`
3. Run the simulation using your simulator's command on file `tb_LEVEL_TO_PULSE_Assertion.svh`.
