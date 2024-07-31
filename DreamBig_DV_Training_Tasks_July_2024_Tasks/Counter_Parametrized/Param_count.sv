`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 03:15:42 PM
// Design Name: 
// Module Name: Param_count
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


module Param_count #(parameter length = 4)(
   input clk,rst,UorD,
    output logic [length-1 : 0] count
    );
  initial begin count = 0; end
    
     always @(posedge clk or posedge rst)
     begin
        if(rst == 1) 
            count <= 0;
        else    
            if(UorD == 1)   
                if(count == 15)
                    count <= 0;
                else
                    count <= count + 1;
            else  
                if(count == 0)
                    count <= 15;
                else
                    count <= count - 1; 
     end    
    
endmodule

