`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 01:57:39 AM
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


module tb();

reg [3:0]a,b;

wire [4:0]result;

full_adder DUT(.a(a),.b(b),.result(result));

initial begin
a = 'b0001;b = 'b0010;
#10;
a = 'b1001;b = 'b1001;
#10;
a = 'b0000;b = 'b0000;
#10;
//$display(result);
a = 'b1111;b = 'b1111;
#10;
end
endmodule
