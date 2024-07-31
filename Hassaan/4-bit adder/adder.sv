`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/09/2024 02:05:50 PM
// Design Name: 
// Module Name: adder
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



module adder #(
    parameter WIDTH = 4
)(
    input logic [WIDTH-1:0] a, b,
    output logic [WIDTH:0] x
);

    // Assign statement for addition
    assign x = a + b;

endmodule
