`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/10/2024 02:25:36 PM
// Design Name: 
// Module Name: alu
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


module alu #(parameter WIDTH = 16) (
    input logic [WIDTH-1:0] a, b,   // 16-bit inputs
    input logic [2:0] sel,          // 3-bit select signal
    output logic [WIDTH-1:0] c      // 16-bit output
);

// Combinational logic for ALU operations
always_comb begin
    case (sel)
        3'b000: c = a + b;          // Addition
        3'b001: c = a - b;          // Subtraction
        3'b010: c = a & b;          // Bitwise AND
        3'b011: c = a | b;          // Bitwise OR
        3'b100: c = a ^ b;          // Bitwise XOR
        default: c = 16'bx;         // Undefined case
    endcase
end

endmodule
