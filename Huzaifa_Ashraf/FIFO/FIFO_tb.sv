`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/04/2024 06:40:22 PM
// Design Name: 
// Module Name: FIFO_tb
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


module FIFO_tb;
  logic clk, reset, write_en,read_en;
  logic [7:0] data_in, data_out;
  logic full, empty;

  FIFO #( .DataWidth(8), .Depth(4) ) my_fifo (.clk(clk),
   .reset(reset), 
   .write_en(write_en),
   .read_en(read_en),
   .data_in(data_in),
    .data_out(data_out),
    .full(full),
    .empty(empty));
    
     always #5 clk = ~clk;
     
     initial begin 
     clk = 0;
     read_en = 0;
     write_en = 0;
     reset = 1;
     full =0;
     empty = 1;
     #10
     $display("read_en= %d, write_en= %d",read_en,write_en);
     #10
     reset = 0;
     write_en = 1;
     read_en =0;
     empty = 1;
     data_in = 'd123;
     
     #10 
     
     write_en = 0;
     read_en =1;
     full = 0;
     empty = 0;
      
     
     end

  endmodule

