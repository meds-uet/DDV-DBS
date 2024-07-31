Overview
This repository contains the SystemVerilog code for an SPI (Serial Peripheral Interface) Master. The SPI Master module is a parameterizable design, allowing for flexible data width configuration. The module handles SPI communication, including data transmission and reception, clock generation, and chip select signaling.

Features
Parameterizable Data Width: The width of the data can be set via a parameter.
State Machine Control: Uses a finite state machine (FSM) to manage the different stages of SPI communication (IDLE, TRANSMIT, FINISH).
Shift Registers: Implements shift registers for both transmitting and receiving data.
Clock and Signal Management: Manages SPI clock (sclk), master out slave in (mosi), master in slave out (miso), and slave select (ss_n) signals.
Interface
Inputs
clk: System clock signal.
rst_n: Active-low reset signal.
start_transaction: Signal to start an SPI transaction.
tx_data: Data to be transmitted (width is parameterizable).
miso: Master In Slave Out signal for receiving data from the slave.
Outputs
rx_data: Data received from the slave (width is parameterizable).
transaction_done: Indicates the completion of an SPI transaction.
sclk: SPI clock signal.
mosi: Master Out Slave In signal for sending data to the slave.
ss_n: Slave select signal, active low.
State Machine
The SPI Master module uses a state machine with three states:

IDLE: Waits for the start_transaction signal.
TRANSMIT: Shifts out tx_data on mosi and shifts in data from miso into rx_data.
FINISH: Completes the transaction and asserts transaction_done.