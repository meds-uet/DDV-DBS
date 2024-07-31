`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/05/2024 12:11:18 AM
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


module ALU(input [15:0]a,b,
           input [2:0] sel,
           output logic [15:0]c);

always_comb begin

case(sel)

'b000 : c = a + b; //addition
'b001 : c = a - b; //subtraction
'b010 : c = a & b; //and operation
'b011 : c = a | b; //or operation
'b100 : c = a ^ b; //xor operation

default : c = 'b0000000000000000;

endcase

end

endmodule
