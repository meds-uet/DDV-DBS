`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/29/2024 07:58:41 PM
// Design Name: 
// Module Name: Randomized_Tezt_ALU
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

module Randomized_Tezt_ALU(
    input  logic [15:0] a,
    input  logic [15:0] b,
    input  logic [3:0]  op,
    output logic [15:0] result,
    output logic        zero,
    output logic        carry,
    output logic        overflow
);

    always_comb begin
        case(op)
            4'b0000: result = a + b;     // Addition
            4'b0001: result = a - b;     // Subtraction
            4'b0010: result = a & b;     // AND
            4'b0011: result = a | b;     // OR
            4'b0100: result = a ^ b;     // XOR
            4'b0101: result = ~a;        // NOT
            4'b0110: result = a << 1;    // Shift left
            4'b0111: result = a >> 1;    // Shift right
            // Other operations
            default: result = 16'h0000;  // Default case
        endcase

        // Flags
        zero = (result == 16'h0000);

        case(op)
            4'b0000: begin
                carry = (a + b) > 16'hFFFF;
                overflow = ((a[15] == b[15]) && (result[15] != a[15]));
            end
            4'b0001: begin
                carry = (a < b);
                overflow = ((a[15] != b[15]) && (result[15] != a[15]));
            end
            default: begin
                carry = 0;
                overflow = 0;
            end
        endcase
    end

endmodule
