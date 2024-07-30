`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/29/2024 06:23:48 PM
// Design Name: 
// Module Name: 16bit_ALU
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

module Sixtn_bit_Arithematic_Logic_Unit (
    input [15:0] A, B,
    input [2:0] control,
    output reg [15:0] result
);
    always @(*) begin
        case (control)
            3'b000: result = A + B;    // Addition
            3'b001: result = A - B;    // Subtraction
            3'b010: result = A & B;    // AND
            3'b011: result = A | B;    // OR
            3'b100: result = A ^ B;    // XOR
            default: result = 16'b0;   // Default to 0 for unused control values
        endcase
    end
endmodule

