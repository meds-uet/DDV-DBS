`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/11/2024 11:08:11 AM
// Design Name: 
// Module Name: FSM_tb
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

module PulseFSM_tb;
logic x, clk, rst;
logic out;

PulseFSM fsm (.clk(clk), .rst(rst), .x(x), .out(out));

initial
begin
clk = 0; rst = 0;
#5
rst = 1;
#5 
rst = 0;
#5
x = 0;
#5 
x= 0;
#5 
x= 1;
#5
x= 0;
#5
x= 1;
#5
x=1;
end
always #5 clk = ~clk;
endmodule
