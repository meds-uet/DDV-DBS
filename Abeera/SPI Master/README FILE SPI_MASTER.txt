
SPI Master Verilog Module
Overview
This repository contains a Verilog module for an SPI Master along with its testbench.

SPI Master
Parameters
DATA_WIDTH: Default is 8 bits. Specifies the width of the data being transmitted/received.
CLOCK_DIVIDER: Default is 4. Controls the frequency of the SPI clock.
NUM_SLAVES: Default is 1. Specifies the number of slave devices.
Ports
Global Signals:
clk: Clock signal.
rst_n: Active-low reset signal.
Control Signals:
start_transaction: Starts the SPI transaction.
tx_data: Data to be transmitted.
rx_data: Received data.
transaction_done: Indicates that the transaction is complete.

SPI Interface:
sclk: SPI clock signal.
mosi: Master Out Slave In signal.
miso: Master In Slave Out signal.
ss_n: Slave select signal.

Functionality
The SPI Master operates in three states: IDLE, TRANSMIT, and FINISH.
Data transmission/reception is handled using shift registers.
Generates an SPI clock with the desired frequency using the CLOCK_DIVIDER parameter.

State Machine
IDLE: Waits for the start_transaction signal.
TRANSMIT: Shifts out data on mosi and shifts in data from miso.
FINISH: Sets transaction_done to indicate the end of the transaction and returns to IDLE.

Testbench
Description
The testbench generates a 100 MHz clock and simulates the SPI Master interaction with a simple SPI Slave model.
Includes a driver, monitor, and scoreboard to validate the SPI transactions.

Components
Driver: Drives transactions by loading data into tx_data and asserting start_transaction.
Monitor: Observes transactions and logs the received data.
Scoreboard: Checks the results of transactions against expected values.

Example Transactions
The testbench performs basic transactions with data values 8'hA5, 8'hFF, 8'h00, and 8'hAA.
Checks for correct data reception and transaction completion.

Notes
The SPI Slave model in the testbench sends and receives data to/from the SPI Master.
Adjust the DATA_WIDTH and CLOCK_DIVIDER parameters as needed for your specific application

