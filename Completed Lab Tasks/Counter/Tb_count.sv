`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/11/2024 02:16:47 PM
// Design Name: 
// Module Name: Tb_count
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


module Tb_count#(parameter w=4);


logic [w-1:0]a1;
logic sel,reset,clk;
logic [w-1:0]b1;

Count DUT (.a(a1),.b(b1),.clk(clk),.reset(reset),.sel(sel));
initial begin 
        reset = 0;
        #2 reset=~reset;
        end

initial begin
        clk=0;
        forever #3 clk=~clk;
        end

initial begin 
        sel=1;
        #100
        $stop;
        end
endmodule
