
Scoreboard for FIFO Verification

Overview
The Scoreboard class is used to verify FIFO module operations in SystemVerilog by tracking expected and actual results, comparing them, and reporting mismatches.

Description
Parameters
DATA_WIDTH: Specifies the bit width of the data.
Internal Data Structures
expected_queue: A dynamic array for expected results.
match_count and mismatch_count: Counters for tracking matches and mismatches.

Methods
Constructor: Initializes match_count and mismatch_count to zero.
add_expected: Adds an expected result to the queue.
compare_result: Compares actual results with expected results, updating the counters and printing mismatches.
report_statistics: Prints a summary of matches, mismatches, and items left in the queue.

Usage in Testbench
Instantiate: Create an instance of Scoreboard.
Add Expected Results: Use add_expected to queue expected results.
Compare Results: Use compare_result to compare actual results from the DUT with expected results.
Report Statistics: Call report_statistics at the end of the test to print the summary.