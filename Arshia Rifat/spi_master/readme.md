This repository contains a SystemVerilog implementation of an SPI (Serial Peripheral Interface) Master module along with its testbench.

## File

1. `spi_master.sv`: The SPI Master module implementation
2. `tb_spi_master.sv`: Testbench for the SPI Master module

## SPI Master Module Features

- Configurable data width
- Adjustable clock divider for SPI clock generation
- Support for multiple slave devices
- Flexible slave selection

### Parameters

- `DATA_WIDTH`: Width of data to be transmitted/received (default: 8 bits)
- `CLOCK_DIVIDER`: Divider for generating SPI clock from system clock (default: 4)
- `NUM_SLAVES`: Number of slave devices supported (default: 4)

### Ports

- `clk`: System clock input
- `rst_n`: Active-low reset
- `sclk`: SPI clock output
- `ss_n`: Active-low slave select lines
- `start_transaction`: Signal to start an SPI transaction
- `tx_data`: Data to be transmitted
- `rx_data`: Received data
- `mosi`: Master Out Slave In data line
- `miso`: Master In Slave Out data line
- `slave_select`: Input to select which slave to communicate with
- `transaction_done`: Signal indicating completion of transaction

## Testbench

The testbench (`tb_spi_master.sv`) includes:

- Clock generation
- Reset sequence
- SPI slave model
- Transaction driver
- Result monitor
- Scoreboard for verification

## Usage

1. You need to have a SystemVerilog compatible simulator (e.g., ModelSim, QuestaSim)
2. Compile both `spi_master.sv` and `tb_spi_master.sv`
3. Run the simulation on the testbench module `tb_spi_master`
