`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 08:02:14 PM
// Design Name: 
// Module Name: alu16 tb
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


module alu16tb;
 reg [15:0] a;
 reg [15:0] b;
 reg [2:0] alu_sel;
 
 wire [15:0] alu_out;
 wire carry_out;
 
 alu uut(.a(a), .b(b), .alu_sel(alu_sel), .alu_out(alu_out), .carry_out(carry_out));
 
 initial begin
   $monitor("Time = %0t: a = %h, b = %h, alu_sel = %h, alu_out = %h, carry_out = %b", $time, a, b, alu_sel, alu_out, carry_out);
   //initialize Input
   a = 16'h0000;
   b = 16'h0000;
   alu_sel = 3'b000;
   //addition
   #10 a = 16'h0001; b = 16'h0001; alu_sel = 3'b000;
   #10 a = 16'hFFFF; b = 16'h0001; alu_sel = 3'b001;
   //test subtraction
   #10 a = 16'h0002; b = 16'h0001; alu_sel = 3'b001;
   #10 a = 16'h0001; b = 16'h0002; alu_sel = 3'b001; 
   //test multipication
   #10 a = 16'h0002; b = 16'h0003; alu_sel = 3'b010;
   //test division
   #10 a = 16'h0006; b = 16'h0003;  alu_sel = 3'b011;
   //test and
   #10 a = 16'hAAAA; b = 16'h5555; alu_sel = 3'b100;
   //or
   #10 a = 16'hAAAA; b = 16'h5555; alu_sel = 3'b010;
   //xor
   #10 a = 16'hAAAA; b = 16'h5555; alu_sel = 3'b110;
   //nand
   #10 a = 16'hAAAA; b = 16'h5555; alu_sel = 3'b111;
   #10 a = 16'h1234; b = 16'h5678; alu_sel = 3'bxxx;
   
   #10 $finish ; 
 end


endmodule














