README FILE FOR AXI_LITE
This repository contains the implementation of an AXI Lite Slave module along with a testbench to verify its functionality. The AXI Lite Slave module includes both read and write operation handling, and the testbench provides various test cases to ensure correct behavior.

AXI Lite Slave Module
Description
The AXI Lite Slave module is designed to interface with an AXI Lite master. It includes the following features:

Handling of read and write operations
Support for four registers: control_reg, status_reg, data_reg_0, and data_reg_1
Error handling for invalid addresses
Ports
Global signals

aclk: AXI clock signal
aresetn: AXI active-low reset signal
Read address channel

araddr: Read address
arvalid: Read address valid signal (master is ready to transfer)
arready: Read address ready signal (slave is ready to accept the address)
Read data channel

rdata: Read data being transferred from slave to master
rresp: Read response, indicating the status of the read transfer
rvalid: Read valid signal (slave is providing valid read data)
rready: Read ready signal (master is ready to accept the read data)
Write address channel

awaddr: Write address
awvalid: Write address valid signal (master is ready to transfer)
awready: Write address ready signal (slave is ready to accept the address)
Write data channel

wdata: Write data being transferred from master to slave
wvalid: Write valid signal (master is providing valid write data)
wready: Write ready signal (slave is ready to accept the write data)
Write response channel

bresp: Write response, indicating the status of the write transfer
bvalid: Write response valid signal (slave has valid write response)
bready: Write response ready signal (master is ready to accept the response)
Internal Registers
control_reg: Control register for configuration
status_reg: Status register for reporting device state
data_reg_0: Data register 0 for general-purpose use
data_reg_1: Data register 1 for general-purpose use
State Machines
The module uses finite state machines (FSMs) to manage read and write operations. The FSMs transition through states such as IDLE, TRANSFER, and RESPONSE based on the AXI Lite signals.

Testbench
Description
The testbench (tb_axi_lite_slave) verifies the functionality of the AXI Lite Slave module. It includes:

Clock generation
Test stimulus to perform read and write operations
Task definitions for write and read transactions
Monitor process to display transactions
Assertions to check for protocol violations
Test Cases
Write to control register (address 0x0000)
Read from control register (address 0x0000)
Write to data register 0 (address 0x0008)
Read from data register 0 (address 0x0008)
Write to invalid address
Read from invalid address

Assertions
Assertions are included to check for protocol violations, such as changes in address signals when valid signals are high but ready signals are low. Add more assertions based on your specific requirements and understanding of the AXI Lite protocol.

