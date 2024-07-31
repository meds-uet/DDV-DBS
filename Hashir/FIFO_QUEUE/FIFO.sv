`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/30/2024 12:42:30 AM
// Design Name: 
// Module Name: FIFO
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


module FIFO #(
  parameter FIFO_DEPTH = 5,
  parameter FIFO_WIDTH = 8
)(
  input logic clk,
  input logic reset,
  input logic [FIFO_WIDTH-1:0] data_in,
  input logic push,
  input logic pop,
  output logic [FIFO_WIDTH-1:0] data_out,
  output logic empty,
  output logic full
);

logic [FIFO_WIDTH-1:0] fifo [0:FIFO_DEPTH-1]; // memory declaration
int i;

logic [2:0] read;
logic [2:0] write;
logic [2:0] fifo_count;


always @(posedge clk or posedge reset) begin
  if (reset) begin
    
    for (i = 0; i < FIFO_DEPTH; i++) begin
      fifo[i] <= 0;
    end
    read <= 0;
    write <= 0;
    fifo_count <= 0;
    data_out <= 0;
    empty <= 1;
    full <= 0;
  end else begin
   
    if (push && !full) begin
      fifo[write] <= data_in;
      write++;
      fifo_count++;
    end

   
    if (pop && !empty) begin
      data_out <= fifo[read];
      read++;
      fifo_count--;
    end

  
    empty <= (fifo_count == 0);
    full <= (fifo_count == FIFO_DEPTH);
  end
end

endmodule
