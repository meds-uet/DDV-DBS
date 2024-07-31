`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/08/2024 02:33:04 PM
// Design Name: 
// Module Name: pulse_counter
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



module pulse_converter(
  input clk, reset,
  input [1:0] in,
  output reg out
);
parameter s0 = 2'b00;
parameter s1 = 2'b01;
parameter s2 = 2'b10;
parameter s3 = 2'b11;

reg [1:0] state, next_state;

always@(posedge clk or posedge reset)
begin
if(reset)
 state <= s0;
 else
 state <= next_state; 
end
  always@(*)
begin
case(state)
s0:begin
out = 0;
if(in == 0)
next_state = s1;
else 
next_state = s0;
end
s1: begin
out = 0;
if(in == 1)
next_state = s2;
else
next_state = s1;
end
s2: begin
out = 1;
if(in == 1)
next_state = s0;
else
next_state = s1;
end
default: out = 1'bx;
endcase
end

endmodule
