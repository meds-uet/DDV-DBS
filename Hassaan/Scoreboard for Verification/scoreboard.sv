`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/24/2024 10:21:13 AM
// Design Name: 
// Module Name: scoreboard
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////
class Scoreboard #(parameter DATA_WIDTH = 1);
  // Internal data structures
  bit [DATA_WIDTH-1:0] expected_queue[$];  // Queue to store expected results
  int match_count = 0;                     // Counter for matching results
  int mismatch_count = 0;                  // Counter for mismatching results

  // Method to add expected result to the queue
  function void add_expected(bit [DATA_WIDTH-1:0] expected);
    expected_queue.push_back(expected);  // Add the expected result to the end of the queue
  endfunction

  // Method to compare actual result with the expected result
  function void compare_result(bit [DATA_WIDTH-1:0] actual);
    bit [DATA_WIDTH-1:0] expected;       // Variable to store the expected result
    
    // Check if there are expected results in the queue
    if (expected_queue.size() == 0) begin
      $fatal("No expected result to compare");  // Abort simulation if no expected result is found
    end

    // Retrieve the front item from the queue as the expected result
    expected = expected_queue.pop_front(); // Remove the expected result from the queue
    
    // Compare the actual result with the expected result
    if (actual === expected) begin
      match_count = match_count + 1;  // Increment match counter if results match
    end else begin
      mismatch_count = mismatch_count + 1;  // Increment mismatch counter if results do not match
      $error("Mismatch: expected=%0b, actual=%0b", expected, actual);  // Log an error with details
    end
  endfunction

 // Method to display the statistics of the scoreboard
  function void report_statistics();
    $display("Scoreboard Statistics:");  // Print header for statistics
    $display("  Matches: %0d", match_count);  // Print the number of matches
    $display("  Mismatches: %0d", mismatch_count);  // Print the number of mismatches
    $display("  Items left in queue: %0d", expected_queue.size());  // Print the number of items left in the queue
  endfunction
endclass