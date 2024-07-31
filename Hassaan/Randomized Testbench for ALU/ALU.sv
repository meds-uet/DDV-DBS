`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/17/2024 05:05:44 PM
// Design Name: 
// Module Name: ALU
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

module ALU #(parameter WIDTH = 16) (
    input logic [WIDTH-1:0] a, b,
    input logic [2:0] sel,
    output logic [WIDTH-1:0] c
);

always_comb begin
    case(sel)
        3'b000 : c = a + b;
        3'b001 : c = a - b;
        3'b010 : c = a & b;
        3'b011 : c = a | b;
        3'b100 : c = a ^ b;
        default : c = 16'bx;
    endcase
end

endmodule
