`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/24/2024 10:13:29 AM
// Design Name: 
// Module Name: flip_flop
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


module flip_flop(
  input logic clk,    // Clock signal
  input logic reset,  // Asynchronous reset signal (active-low)
  input logic d,      // Data input
  output logic q      // Data output
);

  // Always block triggered on the positive edge of the clock or the negative edge of the reset
  always_ff @(posedge clk or negedge reset) begin
    if (!reset) begin
      // If reset is active (low), set output q to 0
      q <= 0;
    end else begin
      // If reset is not active, set output q to the value of input d
      q <= d;
    end
  end
endmodule

