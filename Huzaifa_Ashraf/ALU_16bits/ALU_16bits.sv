`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 02:47:57 PM
// Design Name: 
// Module Name: ALU_16bits
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


module ALU_16bits(input [15:0] inp1,
                  input [15:0] inp2,
                  input [2:0] sel,
                  output reg[15:0] out
    );
    
   
    always@(*) begin 
    case(sel) 
    3'b000: out = inp1 + inp2;  //add
    3'b001: out = inp1 + inp2;
    3'b010: out = inp1 - inp2;   //sub
    3'b011: out = inp1&inp2;    //and
    3'b100: out = inp1&inp2;
    3'b101: out = inp1|inp2;   //or
    3'b110: out = inp1|inp2;   
    3'b111: out = inp1^inp2;   //xor
    default: out = 16'b0;     //0 to all
    
    endcase
    end
    
endmodule
