`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 12:43:46 PM
// Design Name: 
// Module Name: Addr_4bits
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

module half_adder(input inp1,
                  input inp2,
                  output out,
                  output carry_out); 
    xor(out, inp1, inp2);
    and(carry_out, inp1, inp2);
 endmodule
 
 module full_adder(input A,
                   input B,
                   input Cin,
                   output sum,
                   output cout);
                   wire temp_sum, temp_cout,temp_carry;
     half_adder h1(.inp1(A), .inp2(B),.out(temp_sum),.carry_out(temp_cout));
     half_adder h2(.inp1(temp_sum), .inp2(Cin),.out(sum),.carry_out(temp_carry));
     or(cout, temp_cout,temp_carry);
  endmodule


module Addr_4bits(input [3:0]inp1,
                  input [3:0]inp2,
                  input Cin,
                  output [3:0] sum,
                  output Cout);
                  
   wire C1,C2,C3;
   full_adder F1(.A(inp1[0]),.B(inp2[0]),.Cin(Cin),.sum(sum[0]),.cout(C1));
   full_adder F2(.A(inp1[1]),.B(inp2[1]),.Cin(C1),.sum(sum[1]),.cout(C2));
   full_adder F3(.A(inp1[2]),.B(inp2[2]),.Cin(C2),.sum(sum[2]),.cout(C3));
   full_adder F4(.A(inp1[3]),.B(inp2[3]),.Cin(C3),.sum(sum[3]),.cout(Cout)); 
                  
endmodule
