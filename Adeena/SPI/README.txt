Project Title: SPI Master Module with Testbench

Project Overview
This project contains the implementation of an SPI (Serial Peripheral Interface) Master module and a corresponding testbench for its verification. The SPI Master module is designed to facilitate serial communication between a master device and one or more peripheral devices. The testbench ensures the correctness of the SPI Master's functionality through various test scenarios.

Modules and Task Descriptions
1. SPI Master Module (SPIMASTER.sv)
Aim:
To implement an SPI Master module capable of managing serial communication with SPI peripherals.

Description:
The SPI Master module is responsible for generating the necessary signals to communicate with SPI slave devices. It handles the transmission and reception of data over the SPI bus, which includes the SPI clock (SCLK), Master Out Slave In (MOSI), Master In Slave Out (MISO), and Chip Select (CS) signals.

Key Features:

Configurable clock frequency.
Supports multiple SPI modes (CPOL, CPHA).
Handles data transmission and reception.
Generates chip select signals for peripheral devices.
2. Testbench for SPI Master (TB_SPI.sv)
Aim:
To provide a comprehensive testing environment for the SPI Master module.

Description:
The testbench is designed to verify the functionality of the SPI Master module. It generates various test cases, applies them to the SPI Master, and monitors the outputs to ensure they match the expected behavior. This includes checking the correctness of data transmission and reception, as well as the proper generation of SPI signals.

Key Features:

Generates and applies test cases.
Monitors SPI signals (SCLK, MOSI, MISO, CS).
Validates data transmission and reception.
Provides detailed test reports.

Conclusion
This project provides a robust implementation and verification of an SPI Master module using SystemVerilog. The testbench facilitates thorough testing, ensuring reliable and accurate operation of the SPI Master in various communication scenarios.

