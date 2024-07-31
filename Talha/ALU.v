`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.07.2024 20:15:04
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


module ALU(
    input [15:0] a,       // 16-bit input a
    input [15:0] b,       // 16-bit input b
    input [2:0] control,  // 3-bit control signal
    output reg [15:0] result // 16-bit output result
);

    // Define control signals for operations
    localparam ADD = 3'b000;
    localparam SUB = 3'b001;
    localparam AND_OP = 3'b010;
    localparam OR_OP = 3'b011;
    localparam XOR_OP = 3'b100;

    always @(*) begin
        case (control)
            ADD: result = a + b;
            SUB: result = a - b;
            AND_OP: result = a & b;
            OR_OP: result = a | b;
            XOR_OP: result = a ^ b;
            default: result = 16'b0;
        endcase
    end
endmodule
