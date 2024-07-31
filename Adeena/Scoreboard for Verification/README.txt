

Project Title: ALU and FIFO Module with Scoreboard Testbench

Project Overview

This project contains modules for an Arithmetic Logic Unit (ALU), a FIFO (First-In-First-Out) buffer, and a Scoreboard for verification purposes. The aim is to implement, test, and verify these modules using SystemVerilog. The ALU and FIFO modules serve as essential components in digital systems, while the Scoreboard is used for validation of the test results in the testbench.

Modules and Task Descriptions

1. ALU Module (`ALUREF.sv`)

Aim:
To implement an Arithmetic Logic Unit (ALU) capable of performing various arithmetic and logical operations.

Description:
The ALU module supports multiple operations such as addition, subtraction, bitwise AND, OR, XOR, and others as specified in the design. It takes two operands and a control signal as inputs and produces an output based on the selected operation.

Key Features:
- Supports basic arithmetic operations.
- Includes logical operations.
- Handles control signals for operation selection.

 2. FIFO Module (`FIFO.svh`)

Aim:
To implement a FIFO buffer to manage data flow in digital systems.

Description:
The FIFO module manages the storage and retrieval of data in a first-in, first-out order. It ensures efficient data handling in systems requiring buffering capabilities. The module includes features for enqueueing (writing) and dequeueing (reading) data.

Key Features:
- Enqueue and dequeue operations.
- Overflow and underflow management.
- Configurable depth and data width.

3. Scoreboard Module (`SCOREBOARD.sv`)

Aim:
To verify the functionality of the Device Under Test (DUT) by comparing expected and actual results.

Description:
The Scoreboard module is used in the testbench to validate the DUT's performance. It stores the expected results and compares them against the actual outputs from the DUT. This module is essential for automated testing and verification.

Key Features:
- Stores expected results.
- Compares expected and actual results.
- Generates pass/fail signals based on comparison.

4. Testbench for Scoreboard (`TB_SCOREBOARD.sv`)

Aim:
To provide a comprehensive testing environment for the DUT and the Scoreboard module.

Description:
The testbench integrates the DUT and the Scoreboard module to perform various tests. It generates test cases, applies them to the DUT, and uses the Scoreboard to validate the outputs. This ensures that the DUT meets the design specifications and performs correctly under different scenarios.

Key Features:
- Generates and applies test cases.
- Integrates DUT and Scoreboard.
- Provides detailed test reports.

Conclusion

This project provides a comprehensive implementation and verification of ALU and FIFO modules using SystemVerilog. The Scoreboard module and testbench facilitate automated testing, ensuring reliable and accurate results.
