`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/02/2024 12:40:27 PM
// Design Name: 
// Module Name: tb_siso
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


module tb_siso();
 reg serial_in;
 reg clk, reset;
 wire serial_out;
 
 SISO dut(.serial_in(serial_in), .clk(clk), .rst(reset), .serial_out(serial_out));
 
 initial begin
     clk = 0;
	forever #10 clk = ~clk;
 end 
 
 initial begin
   serial_in <= 0;
   @(posedge clk) reset <= 1;
   @(posedge clk) reset <= 0; 
   #10 serial_in <= 1;
   #10 serial_in <= 0;
   #10 serial_in <= 0;
   #10 serial_in <= 0;
   #30
   @(posedge clk) reset <= 1;
   
 end
 
endmodule
