`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 01:20:45 PM
// Design Name: 
// Module Name: sevensegdecoder
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


module seven_seg_decoder(
    input logic [3:0] binaryin,
    output logic [6:0] segments 
    );
    always@(*)begin
    case (binaryin)
      4'b0000: segments = 7'b1111110; //0
      4'b0001: segments = 7'b0110000; //1
      4'b0010: segments = 7'b1101101; //2
      4'b0011: segments = 7'b1111001; //3
      4'b0100: segments = 7'b0110011; //4
      4'b0101: segments = 7'b1011011; //5
      4'b0110: segments = 7'b1011111; //6
      4'b0111: segments = 7'b1110000;//7
      4'b1000: segments = 7'b1111111; //8
      4'b1001: segments = 7'b1111011; //9
      4'b1010: segments = 7'b1110111; //10
      4'b1011: segments = 7'b0011111;//11
      4'b1100: segments = 7'b1001110; //12
      4'b1101: segments = 7'b0111101; //13
      4'b1110: segments = 7'b1001111; //14
      4'b1111: segments = 7'b1000111; //15
      default: segments = 7'b0000000;
    endcase
    end
endmodule
