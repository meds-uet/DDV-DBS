`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/11/2024 01:29:32 PM
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



class scoreboard #(parameter DATA_WIDTH = 8);
      // Internal data structures
      bit [DATA_WIDTH-1:0] expected_queue[$];
      bit [DATA_WIDTH-1:0] expected;
      int match_count;int mismatch_count;
    
      // Method to add expected result
      function void add_expected(bit [DATA_WIDTH-1:0] expected);
        expected_queue.push_back(expected);
      endfunction
    
      // Method to compare actual result with expected
      function void compare_result(bit [DATA_WIDTH-1:0] actual);
        
        if (expected_queue.size() == 0) begin    
        // TODO: Throw an error and return
        $error("there isn't any value to compare ");
        return;
            
        end
        expected = expected_queue.pop_front();  
      
    
        if (actual === expected) begin
        // TODO: Increment Match Counter
        match_count=match_count+1;
        end else begin
        // // TODO: Increment Mismatch Counter and display error
        mismatch_count=mismatch_count+1;
        $error("there is a mismatach");
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
    
 