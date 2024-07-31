`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.07.2024 20:32:04
// Design Name: 
// Module Name: SevenSegmentDecoder
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


module SevenSegmentDecoder (
    input [3:0] binary_input,  // 4-bit binary input
    output reg [6:0] segment   // 7-bit output for the 7-segment display (a-g)
);

    always @(*) begin
        case (binary_input)
            4'b0000: segment = 7'b1111110; // 0
            4'b0001: segment = 7'b0110000; // 1
            4'b0010: segment = 7'b1101101; // 2
            4'b0011: segment = 7'b1111001; // 3
            4'b0100: segment = 7'b0110011; // 4
            4'b0101: segment = 7'b1011011; // 5
            4'b0110: segment = 7'b1011111; // 6
            4'b0111: segment = 7'b1110000; // 7
            4'b1000: segment = 7'b1111111; // 8
            4'b1001: segment = 7'b1111011; // 9
            4'b1010: segment = 7'b1110111; // A
            4'b1011: segment = 7'b0011111; // b
            4'b1100: segment = 7'b1001110; // C
            4'b1101: segment = 7'b0111101; // d
            4'b1110: segment = 7'b1001111; // E
            4'b1111: segment = 7'b1000111; // F
            default: segment = 7'b0000000; // Default case (all segments off)
        endcase
    end
endmodule
