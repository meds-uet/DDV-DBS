`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 01:32:13 PM
// Design Name: 
// Module Name: seven_segment_decoder
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


module seven_segment_decoder(
input [3:0]in,
output reg [6:0]out   );

always@(*)
begin
case(in)
4'b0000 : out=7'b1111110;
4'b0001 : out=7'b0110000;
4'b0010 : out=7'b1101101;     
4'b0011 : out=7'b1111001;
4'b0100 : out=7'b0110011;
4'b0101 : out=7'b1011011;
4'b0110 : out=7'b1011111;
4'b0111 : out=7'b1110000;
4'b1000 : out=7'b1111111;
4'b1001 : out=7'b1111011;
4'b1010 : out=7'b1110111;
4'b1011 : out=7'b0011111;
4'b1100 : out=7'b1001110;
4'b1101 : out=7'b0111101;
4'b1110 : out=7'b1001111;
4'b1111 : out=7'b1000111;
default:out=7'b1111110;

endcase
end

endmodule
