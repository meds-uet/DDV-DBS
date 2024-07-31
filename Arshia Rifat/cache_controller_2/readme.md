This repository contains a SystemVerilog implementation of a cache controller system, including the cache controller, cache memory, main memory, and a testbench.

## Files

1. `cache_controller.svh`: The main cache controller module.
2. `cache_controller_tb.svh`: Testbench for the cache controller.
3. `cache_memory.svh`: Implementation of the cache memory.
4. `cache_system.svh`: Top-level module integrating the cache controller, cache memory, and main memory.
5. `main_memory.svh`: Implementation of the main memory.

## Overview

This cache controller system implements a direct-mapped write-back cache with the following features:

- 256 cache lines
- 16 bytes per cache line
- 20-bit tag, 8-bit index, and 4-bit offset
- Single dirty bit for the entire cache
- Support for read, write, and flush operations

## Modules

### Cache Controller (`cache_controller.svh`)

The main control unit that handles CPU requests, manages cache hits/misses, and coordinates data transfers between the CPU, cache, and main memory.

### Cache Memory (`cache_memory.svh`)

Implements the cache storage, with 256 lines and 4 words per line.

### Main Memory (`main_memory.svh`)

Simulates a 16KB main memory with configurable access delays.

### Cache System (`cache_system.svh`)

Top-level module that integrates the cache controller, cache memory, and main memory.

## Usage

To use this cache controller system:

1. Compile all five `.svh` files together.
2. Run the simulation using the `cache_controller_tb` as the top-level module.

## Testing

The testbench includes several test cases to verify the functionality of the cache controller:

- Address mapping
- Basic read and write operations
- Boundary accesses
- Write-back on cache misses

It also includes assertions to check for correct behavior and a coverage group to ensure comprehensive testing.

