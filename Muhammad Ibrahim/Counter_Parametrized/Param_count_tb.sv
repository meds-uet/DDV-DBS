`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 03:25:25 PM
// Design Name: 
// Module Name: Param_count_tb
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


module Param_count_tb#(parameter length = 4);
    logic clk;
    logic rst;
    logic UorD;

    logic [length-1:0] count;

    Param_count uut ( .clk(clk), .rst(rst), .UorD(UorD), .count(count));

    initial begin clk = 0; end
    always #5 clk = ~clk;
    
    initial begin
        rst = 0;
        @(posedge clk) rst = 1;
        @(posedge clk) rst = 0;
        UorD = 1;
        #300;
        UorD = 0;
      #300;
       @(posedge clk) rst = 1;
        @(posedge clk) rst = 0;
        UorD = 0;
        #300;
        UorD = 1; 
        @(posedge clk) rst = 1;
    end
      
endmodule
