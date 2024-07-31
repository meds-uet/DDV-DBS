`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/05/2024 12:00:10 PM
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


module ALU( input logic [15:0] a,b,
            input logic [2:0] control,
            output logic [15:0] c );
            
          always_comb begin
            case (control)
                 3'b000: c = (a + b); // addition 
                 3'b001: c = (a - b); // Subtraction
                 3'b010: c = (a & b); // AND
                 3'b011: c = (a | b); // OR
                 3'b100: c = (a ^ b); // XOR
            endcase
          end
endmodule
