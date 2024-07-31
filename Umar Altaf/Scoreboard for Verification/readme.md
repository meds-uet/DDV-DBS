Overview
This repository contains the SystemVerilog implementation of an ALU Scoreboard used for verifying the correctness of an Arithmetic Logic Unit (ALU). The Scoreboard compares the output of the ALU against expected results generated from a reference model or function. It provides detailed statistics and reports any discrepancies between actual and expected outputs.

Features
Comparison: Compares ALU output against expected results.
Statistics: Provides detailed statistics on test cases executed.
Error Reporting: Detects and reports mismatches between actual and expected results.
Modular Design: Easily adaptable for different ALU configurations and test scenarios.
Modules
ALU Module: Implements the actual ALU operations.
Scoreboard Module: Monitors ALU outputs, compares with expected results, and reports discrepancies.
Testbench: Drives stimuli to the ALU and verifies results using the scoreboard.
Usage
Prerequisites
Simulation environment (e.g., ModelSim, VCS) configured for SystemVerilog.
Ensure scoreboard.sv and ALU.sv are included in the simulation setup.
