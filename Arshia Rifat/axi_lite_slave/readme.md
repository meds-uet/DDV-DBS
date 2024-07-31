This repository contains a SystemVerilog implementation of an AXI4-Lite slave module along with a testbench for verification.

## Files

1. `axi_lite_slave.sv`: The main AXI4-Lite slave module implementation
2. `tb_axi_lite_slave.sv`: A comprehensive testbench for the AXI4-Lite slave module

## AXI4-Lite Slave Module

The `axi_lite_slave` module implements a basic AXI4-Lite slave interface with the following features:
- Support for read and write operations
- Four 32-bit registers:
  - Control register (address 0x00000000)
  - Status register (address 0x00000004)
  - Data register 0 (address 0x00000008)
  - Data register 1 (address 0x0000000C)
- Error responses for invalid addresses

## Testbench

The `tb_axi_lite_slave` testbench provides a verification environment for the AXI4-Lite slave module. It includes:
- Clock generation
- Reset sequence
- Multiple test cases for read and write operations
- Transactions to valid and invalid addresses
- A monitor process to display transactions
- An assertion to check for protocol violations

## Usage

To use this module in your project:
1. Include the `axi_lite_slave.sv` file in your project
2. Instantiate the `axi_lite_slave` module in your top-level design
3. Connect the AXI4-Lite interface signals appropriately

To run the testbench:
1. You need to have a SystemVerilog compatible simulator
2. Compile both `axi_lite_slave.sv` and `tb_axi_lite_slave.sv`
3. Run the simulation on the testbench `tb_axi_lite_slave.sv`
