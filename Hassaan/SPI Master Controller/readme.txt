### Verification Strategy

The SPI Master Controller was verified using a direct testbench approach. The testbench includes multiple test cases to validate key functionalities such as data transmission and reception, handling back-to-back transactions, and simulating error conditions. A task-based mechanism was used to perform transactions and check the received data against expected results. This straightforward method allowed for efficient verification of basic operations before addressing more complex scenarios.

### Challenges Encountered

Implementing a layered testbench for the SPI Master Controller proved challenging due to the intricate interactions between different SPI signals and the need for precise synchronization. The complexity of managing these interactions led to difficulties in ensuring comprehensive coverage and accurate testing. As a result, I opted for a direct testbench approach to effectively validate the core functionality of the SPI Master Controller before tackling the layered testbench implementation.