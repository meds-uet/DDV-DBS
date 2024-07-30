`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/28/2024 07:29:56 AM
// Design Name: 
// Module Name: counter
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


module counter #(parameter WIDTH=8)(input clk,reset,
               input logic [WIDTH-1:0]init_val,
               output logic [WIDTH-1:0] out,
               input logic up_or_down
    );
    
    always @(posedge clk or negedge reset)begin
    
    if(!reset)begin
    
        out <= init_val;
    
    end
    
    else begin
    
        if(up_or_down) begin
        
            out <= out + 1;
        
        end
        
        else begin
        
            out <= out - 1;
        
        end
     
    
    end
    
    end
    
    
endmodule
