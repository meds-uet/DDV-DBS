This repository contains a UVM (Universal Verification Methodology) implementation of a cache controller system, including the cache controller, UVM components, interfaces, and testbench.

## Files

1. `cache_agent.svh`: UVM agent class for the cache controller.
2. `cache_controller.svh`: The main cache controller module implementation.
3. `cache_driver.svh`: UVM driver class for the cache controller.
4. `cache_env.svh`: UVM environment class for the cache controller testbench.
5. `cache_if.svh`: SystemVerilog interface for the cache controller.
6. `cache_monitor.svh`: UVM monitor class for observing cache controller behavior.
7. `cache_scoreboard.svh`: UVM scoreboard class for checking cache controller functionality.
8. `cache_seq_item.svh`: UVM sequence item class defining cache transactions.
9. `cache_sequence.svh`: UVM sequence classes for generating different test scenarios.
10. `cache_memory.svh`: SystemVerilog module implementing the cache memory.
11. `cache_system.svh`: Top-level module integrating cache controller, cache memory, and main memory.
12. `cache_tests.svh`: UVM test classes for different test scenarios.
13. `main_memory.svh`: SystemVerilog module implementing the main memory.
14. `top.svh`: Top-level SystemVerilog module for simulation.

## Overview

This project implements a UVM-based testbench for a cache controller system with the following features:

- Write-back cache with 256 cache lines
- 16 bytes per cache line
- 20-bit tag, 8-bit index, and 4-bit offset
- Single dirty bit for the entire cache
- Support for read, write, and flush operations
- UVM-compliant verification environment

## UVM Components

### Cache Agent (`cache_agent.svh`)

Coordinates the driver, sequencer, and monitor components for the cache controller.

### Cache Driver (`cache_driver.svh`)

Responsible for driving stimulus to the DUT (Device Under Test) through the virtual interface.

### Cache Environment (`cache_env.svh`)

Top-level UVM environment that includes the agent and scoreboard.

### Cache Interface (`cache_if.svh`)

SystemVerilog interface defining the signals for interaction with the cache controller.

### Cache Monitor (`cache_monitor.svh`)

Observes the cache controller's behavior and sends collected transactions to the scoreboard.

### Cache Scoreboard (`cache_scoreboard.svh`)

Verifies the correctness of cache operations by comparing expected results with actual outcomes.

### Cache Sequence Item (`cache_seq_item.svh`)

Defines the structure of cache transactions used in the testbench.

### Cache Sequences (`cache_sequence.svh`)

Contains various sequence classes for generating different test scenarios.

### Cache Tests (`cache_tests.svh`)

Defines different UVM test classes:
- `cache_base_test`: Basic test
- `cache_write_test`: Write-only test
- `cache_read_test`: Read-only test
- `cache_mixed_test`: Mixed read and write test
- `cache_flush_test`: Cache flush test

## Design Under Test

### Cache Controller (`cache_controller.svh`)

The main cache controller module that handles CPU requests, manages cache hits/misses, and coordinates data transfers.

### Cache Memory (`cache_memory.svh`)

SystemVerilog module implementing the cache memory structure.

### Cache System (`cache_system.svh`)

Top-level module integrating the cache controller, cache memory, and main memory.

### Main Memory (`main_memory.svh`)

SystemVerilog module implementing the main memory with configurable access delays.

## Testbench

### Top (`top.svh`)

Top-level SystemVerilog module that instantiates the DUT, interface, and starts the UVM test.

## Usage

To use this UVM-based cache controller testbench:

1. Compile all the provided `.svh` files along with your UVM library.
2. Use the `top.svh` file as the top-level module for simulation.

## Verification Strategy

The UVM-based testbench allows for:

- Structured and reusable test scenarios
- Randomized testing of the cache controller
- Comprehensive functional coverage
- Automatic checking and scoreboarding of cache operations
