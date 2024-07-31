`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/04/2024 02:47:06 PM
// Design Name: 
// Module Name: tb
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
module tb( );

logic [3:0] a1;
logic [6:0] b1;

Seven_Seg DUT (.a(a1),.b(b1));

initial begin 

a1='b0000; 
#10
a1='b0001;
#10
a1='b0010;
#10              
a1='b0011;
#10
a1='b0100;
#10
a1='b0101;
#10
a1=4'b0110;
#10
a1='b0111;
#10
a1='b1000;
#10
$stop;
end
endmodule
