`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/10/2024 12:21:35 PM
// Design Name: 
// Module Name: Seven_Seg
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

module Seven_Seg (
    input logic [3:0] x,
    output logic [6:0] y
);

always_comb begin
    case(x)
        4'b0000 : y = 7'b1110110;
        4'b0001 : y = 7'b1111111;
        4'b0010 : y = 7'b1001111;
        4'b0011 : y = 7'b1111110;
        4'b0100 : y = 7'b1001111;
        4'b0101 : y = 7'b1000111;
        4'b0110 : y = 7'b1111011;
        4'b0111 : y = 7'b0000110;
        4'b1000 : y = 7'b1101101;
        4'b1001 : y = 7'b1111001;
        4'b1010 : y = 7'b0110011;
        4'b1011 : y = 7'b1011011;
        4'b1100 : y = 7'b1011111;
        4'b1101 : y = 7'b1110000;
        4'b1110 : y = 7'b1111111;
        4'b1111 : y = 7'b1110011;
    endcase
end

endmodule
