`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/02/2024 12:11:53 PM
// Design Name: 
// Module Name: Shift_register
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

module Shift_register (
    input clk,          
    input reset,       
    input serial_in,    
    output [3:0] parallel_out  
);

logic [3:0] shift_reg;  

always @(posedge clk or posedge reset) begin
    if (reset) begin
        shift_reg <= 4'b0000;  
    end else begin
        shift_reg <= {shift_reg[2:0], serial_in};  
    end
end

assign parallel_out = shift_reg;  

endmodule
