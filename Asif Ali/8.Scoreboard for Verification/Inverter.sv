`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/29/2024 10:25:27 PM
// Design Name: 
// Module Name: Inverter
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


module Inverter (
  input logic clk,
  input logic reset,
  input logic [7:0] data_in,
  output logic [7:0] data_out,
  input logic invert
);

  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      data_out <= 8'h00;
    end else begin
      if (invert)
        data_out <= ~data_in;
      else
        data_out <= data_in;
    end
  end

endmodule
