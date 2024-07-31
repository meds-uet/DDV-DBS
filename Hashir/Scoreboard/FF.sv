`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/30/2024 05:35:14 PM
// Design Name: 
// Module Name: FF
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


module FF(input logic clk,reset,
          input logic a,
          output logic b);
          
   always @(posedge clk or posedge reset) begin 
   if (reset) begin 
   b<=0;
   
   end
   
   else begin 
   b<=a;
   end
   end
          
endmodule
