`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/04/2024 11:40:36 AM
// Design Name: 
// Module Name: parameterized_counter
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


module parameterized_counter #(parameter size = 8)(
                            input up,down,reset,
                            input clk,
                            input [size-1:0] inp1,
                            output [size-1:0] count);
                            
   reg [size-1:0] temp_count;
   
   always@(posedge clk or posedge reset) begin
        if(reset)
            temp_count <= inp1;
         else if(up)
            temp_count <= temp_count + 1;
         else if(down)
            temp_count <= temp_count - 1;
    end
     assign count = temp_count;
   
endmodule
