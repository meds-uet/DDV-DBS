`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/24/2024 10:42:35 AM
// Design Name: 
// Module Name: tb_dut
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

`include "D:/Vivado/Dreambig/Scoreboard/Scoreboard.srcs/sources_1/new/scoreboard.sv"

// Testbench module for the DUT (Device Under Test)
module tb_dut;
  // DUT (Device Under Test) signals
  logic clk, reset;          // Clock and reset signals
  logic data_in, data_out;  // Data input and output signals

  // Instantiate the DUT (flip-flop)
  flip_flop DUT (
    .clk(clk),       // Connect clock signal to DUT
    .reset(reset),   // Connect reset signal to DUT
    .d(data_in),     // Connect data input to DUT
    .q(data_out)     // Connect data output from DUT
  );

  // Instantiate the Scoreboard
  Scoreboard #(.DATA_WIDTH(1)) scoreboard;  // Create a Scoreboard instance for 1-bit data width

  // Clock generation
  initial begin
    clk = 0;              // Initialize clock to 0
    forever #5 clk = ~clk;  // Toggle clock every 5 time units (10 time units period)
  end

  // Test stimulus and scoreboard usage
  initial begin
    // Initialize
    scoreboard = new();   // Create a new instance of the Scoreboard
    reset = 0;           // Set reset signal to 0 initially
    data_in = 0;         // Set data input to 0 initially
    @(posedge clk);      // Wait for the first positive edge of the clock
    reset = 1;          // Assert reset (set to 1) after the first positive edge of the clock
    
    // Test case 1: Simple data pass-through
    data_in = 1'b1;     // Set data input to 1
    @(posedge clk);     // Wait for the next positive edge of the clock
    scoreboard.add_expected(data_in);  // Add the expected result (data_in) to the scoreboard
    scoreboard.compare_result(data_out);  // Compare the actual result (data_out) with the expected result

    // Test case 2: Data inversion
    data_in = ~data_in; // Invert data input (0 becomes 1, and 1 becomes 0)
    @(posedge clk);     // Wait for the next positive edge of the clock
    scoreboard.add_expected(data_in);  // Add the expected result (data_in) to the scoreboard
    scoreboard.compare_result(data_out);  // Compare the actual result (data_out) with the expected result
    
    // Random test cases
    repeat(10) begin
      data_in = $random % 2;  // Generate a random 1-bit value (0 or 1)
      @(posedge clk);        // Wait for the next positive edge of the clock
      scoreboard.add_expected(data_in);  // Add the expected result (data_in) to the scoreboard
      scoreboard.compare_result(data_out);  // Compare the actual result (data_out) with the expected result
    end
    
    // Report scoreboard statistics
    scoreboard.report_statistics();  // Print the statistics of the scoreboard (matches, mismatches, and remaining items in the queue)
    
    
    $finish;  // End the simulation
  end
endmodule
