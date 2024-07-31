`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 01:44:32 PM
// Design Name: 
// Module Name: disp7Seg
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


module Dec7Seg(
  input [3:0]BCD,
  output logic [6:0]SEG
    );
    always @(BCD)
    begin
        case (BCD) //case statement
            0 : SEG = 7'b0000001;
            1 : SEG = 7'b1001111;
            2 : SEG = 7'b0010010;
            3 : SEG = 7'b0000110;
            4 : SEG = 7'b1001100;
            5 : SEG = 7'b0100100;
            6 : SEG = 7'b0100000;
            7 : SEG = 7'b0001111;
            8 : SEG = 7'b0000000;
            9 : SEG = 7'b0000100;
            default : SEG = 7'b1111111; 
        endcase
    end
    
endmodule