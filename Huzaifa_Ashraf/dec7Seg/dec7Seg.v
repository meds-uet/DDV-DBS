`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06/27/2024 10:45:02 PM
// Design Name: 
// Module Name: dec7Seg
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

module dec7Seg(input wire [3:0] in, output wire [6:0] out);

reg [6:0] out_t;

assign out = out_t;

always@(in) begin
    case(in)         // gfedcba
    4'b0000: out_t = 7'b1000000;  //0
    4'b0001: out_t = 7'b1111001;  //1
    4'b0010: out_t = 7'b0100100;  //2
    4'b0011: out_t = 7'b0110000;  //3
    4'b0100: out_t = 7'b0011001;  //4
    4'b0101: out_t = 7'b0010010;  //5
    4'b0110: out_t = 7'b0000010;  //6
    4'b0000: out_t = 7'b1111000;  //7
    4'b0111: out_t = 7'b0000000;  //8
    4'b1000: out_t = 7'b0011000;  //9
    4'b1001: out_t = 7'b0001000;  //A
    4'b1010: out_t = 7'b0000000;  //B
    4'b1011: out_t = 7'b1000110;  //C
    4'b1100: out_t = 7'b0100001;  //D
    4'b1101: out_t = 7'b0000110;  //E
    4'b1110: out_t = 7'b1001110;  //F
    
    
    endcase
end

endmodule
