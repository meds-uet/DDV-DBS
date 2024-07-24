`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 02:21:27 PM
// Design Name: 
// Module Name: ssd tb
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


module ssdtb;
  logic [3:0] binaryin;
  logic [6:0] segments;
  
  seven_seg_decoder ssd(.binaryin(binaryin),
                        .segments(segments));
  initial begin
  for(binaryin = 0; binaryin < 15; binaryin = binaryin + 1)
     #20;
     $finish;
  end                        
endmodule

















