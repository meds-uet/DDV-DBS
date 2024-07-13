`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 12:21:37 PM
// Design Name: 
// Module Name: Adder_4_bit_tb
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


module Adder_4_bit_tb;
   logic [4:0]A;
   logic [4:0]B;
   logic c_in;
   logic [5:0]S;
   integer i;

   Adder_4_bit  fa0(.A(A), .B(B), .c_in(c_in), .S(S));

   initial 
   begin
      A = 0;
      B = 0;
      c_in = 0;
      

      for (i = 0; i < 20; i = i+1) begin
         #10 A <= $random;
             B <= $random;
         	 c_in <= $random;
         	 if (S == A+B+c_in)
         	 $display("the sum of A = %d  and B = %d and c_in = %d is S = %d as expected", A, B, c_in, S);
         	 else
         	 $display("the sum of A = %d  and B = %d and c_in = %d is S = %d as not expected", A, B, c_in, S);
      end
   end
  
  
endmodule
