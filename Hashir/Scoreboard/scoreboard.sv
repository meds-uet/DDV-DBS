`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/29/2024 02:36:46 PM
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


module scoreboard();

class Scoreboard #(parameter DATA_WIDTH = 8);
  // Internal data structures
  bit [DATA_WIDTH-1:0] expected_queue[$];     //  to store expected results
  int match_count, mismatch_count;            //hit and miss counter

  function count_initialize();
    match_count = 0;
    mismatch_count = 0;
  endfunction

  // Method to add expected result in the queue
  function void add_expected(bit [DATA_WIDTH-1:0] expected);   
    expected_queue.push_back(expected);       // Push the expected result at the end of the array
  endfunction

  // Method to compare actual result with expected
  function void compare_result(bit [DATA_WIDTH-1:0] actual);
  
     logic [DATA_WIDTH-1:0] expected;
    if (expected_queue.size() == 0) begin       //means no expected result in queue
      $display("Error as there is no expexted result to compare against.");
      return;
    end

   expected = expected_queue.pop_front(); // Remove and return the first element from the queue

    if (actual === expected) begin
      match_count=match_count+1;        //for hit
    end else begin
      mismatch_count=mismatch_count+1;  //for miss
      $display("Mismatch: Expected %0d, Got %0d", expected, actual); // Display error
    end
  endfunction

  // Method to display scoreboard statistics
  function void report_statistics();
    $display("Scoreboard Statistics:");
    $display("  Matches: %0d", match_count);
    $display("  Mismatches: %0d", mismatch_count);
    $display("  Items left in queue: %0d", expected_queue.size());
  endfunction
endclass

endmodule

