`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 02:19:53 PM
// Design Name: 
// Module Name: tb
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


module tb;
  logic [3:0] a1,b1;
  logic [4:0] c1;
    
   binary_adder DUT  (.a(a1),.b(b1),.c(c1));
   
   initial begin
   a1='b1010;
   b1='b0101;
   #10;
   a1='b0100;
   b1='b1000;
   #10;
   $stop;
   end
endmodule
