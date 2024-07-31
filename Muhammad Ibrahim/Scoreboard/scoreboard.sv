`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/18/2024 12:49:13 PM
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


class Scoreboard #(parameter DATA_WIDTH = 8);
    // Internal data structures
    bit [DATA_WIDTH-1:0] expected_queue[$];
    int match_count, mismatch_count;

    // Constructor
    function new();
        match_count = 0;
        mismatch_count = 0;
    endfunction

    // Method to add expected result
    function void add_expected(input bit [DATA_WIDTH-1:0] expected);
        expected_queue.push_back(expected);
    endfunction
  bit [DATA_WIDTH-1:0] expected;
    // Method to compare actual result with expected
    function void compare_result(input bit [DATA_WIDTH-1:0] actual);
        if (expected_queue.size() == 0) begin
            $error("No expected data to compare against.");
            return;
        end

         expected = expected_queue.pop_front();

        if (actual == expected ) begin
            match_count++;
        end else begin
            mismatch_count++;
            $display("Mismatch: Expected %0h, got %0h", expected, actual);
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
