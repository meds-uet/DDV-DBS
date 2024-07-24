This project contains the implementation of an AXI4-Lite slave module and its corresponding testbench.
AXI4-Lite Slave Module
The AXI4-Lite slave module includes the following features:

Read Address Channel
Read Data Channel
Write Address Channel
Write Data Channel
Write Response Channel

FSM States
The finite state machine (FSM) manages read and write operations through the following states:

IDLE: Waiting for a valid transaction.
TRANSFER: Processing the read/write transaction.
RESPONSE: Sending the response back to the master.

Tasks
write_transaction: Handles write transactions to the slave.
read_transaction: Handles read transactions from the slave.

Assertion
An assertion is included to check for protocol violations, ensuring address stability during write transactions.
