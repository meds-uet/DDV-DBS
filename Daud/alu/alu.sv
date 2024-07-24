`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 07:42:46 PM
// Design Name: 
module alu(
  input [15:0] a,
  input [15:0] b,
  input [2:0] alu_sel,
  output reg [15:0] alu_out,
  output reg carry_out
    );
  always@(*)begin
  case(alu_sel)
    3'b000: {carry_out, alu_out} = a + b;
    3'b001: {carry_out, alu_out} = a - b; 
    3'b010: alu_out = a * b;
    3'b011: alu_out = a / b;
    3'b100: alu_out = a & b;
    3'b101: alu_out = a | b;
    3'b110: alu_out = a ^ b;
    3'b111: alu_out = ~(a & b);
    default: alu_out = 16'b0;
  endcase
  end  
endmodule
