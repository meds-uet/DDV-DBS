`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/04/2024 11:57:33 AM
// Design Name: 
// Module Name: Seven_Seg
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


module Seven_Seg( input logic [3:0] a,
                  output logic [6:0] b);
                  
           always_comb begin
           case (a)
              4'b0000: b = 7'b1111110;
              4'b0001: b = 7'b1100000;
              4'b0010: b = 7'b1101101;
              4'b0011: b = 7'b1111001;
              4'b0100: b = 7'b0110011;
              4'b0101: b = 7'b1011011;
              4'b0110: b = 7'b1011111;
              4'b0111: b = 7'b1110000;
              4'b1000: b = 7'b1111111;
          endcase
          end
           
endmodule
