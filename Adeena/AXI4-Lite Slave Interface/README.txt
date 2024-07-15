
Project Title: AXI4-Lite Interface Module with Testbench

Project Overview

This project contains the implementation of an AXI4-Lite interface module and a corresponding testbench for its verification. The AXI4-Lite interface module is designed to facilitate communication between master and slave devices using the AXI4-Lite protocol. The testbench ensures the correctness of the AXI4-Lite module's functionality through various test scenarios.

Modules and Task Descriptions

1. AXI4-Lite Interface Module (`AXI4LITE.sv`)

Aim:
To implement an AXI4-Lite interface module for communication between master and slave devices.

Description: 
The AXI4-Lite interface module is responsible for handling read and write transactions between AXI4-Lite master and slave devices. It supports single data transfers and manages the necessary control signals for AXI4-Lite communication, including address, data, write, and read signals.

Key Features:
- Supports AXI4-Lite read and write transactions.
- Manages control signals (AW, W, B, AR, R).
- Handles address and data transfers.
- Ensures compliance with AXI4-Lite protocol specifications.

2. Testbench for AXI4-Lite Interface (`TB_AXI4LITE.sv`)

Aim:
To provide a comprehensive testing environment for the AXI4-Lite interface module.

Description:
The testbench is designed to verify the functionality of the AXI4-Lite interface module. It generates various test cases, applies them to the AXI4-Lite module, and monitors the outputs to ensure they match the expected behavior. This includes checking the correctness of read and write transactions and the proper handling of control signals.

Key Features:
- Generates and applies test cases.
- Monitors AXI4-Lite signals (AW, W, B, AR, R).
- Validates read and write transactions.
- Provides detailed test reports.


Conclusion

This project provides a robust implementation and verification of an AXI4-Lite interface module using SystemVerilog. The testbench facilitates thorough testing, ensuring reliable and accurate operation of the AXI4-Lite module in various communication scenarios.