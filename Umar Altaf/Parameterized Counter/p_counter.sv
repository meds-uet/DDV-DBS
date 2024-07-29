`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/04/2024 09:25:38 AM
// Design Name: 
// Module Name: p_counter
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


module p_counter
# (parameter width=8)
(

input logic reset,clk,up,down,set,

input logic [width-1:0] set_value,
output logic [width+1:0]count);


 
 always @(posedge clk ) 
begin
   if (reset) 
begin
count <= 0;
end 
else if( set)
begin
count<=set_value;
end
else if (up)
begin
count<=count+1'b1;
end
else if (down && count!==0)
begin
count<=count-1'b1;
end
end
endmodule
