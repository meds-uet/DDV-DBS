`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 12:03:53 PM
// Design Name: 
// Module Name: tb_four_bit_adder
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


module tb_four_bit_adder;
reg [3:0]a,b;
reg clk;
reg [4:0]out;
reg [4:0]test;

 four_bit_adder fa (a,b,out);

initial begin 
  clk = 0;
 forever 
    #5 clk = ~clk;
end
initial
begin
$monitor("a = %b,b = %b,out = %b", a,b,out);
end
initial
begin

@(posedge clk);
a=$urandom();
b=$urandom();
test=a+b;
if (test==out)
begin
$display("test case 1 is passed");
end 
@(posedge clk);
a=$urandom();
b=$urandom();
test=a+b;
if (test==out)
begin
$display("test case 2 is passed");
end
@(posedge clk);
a=$urandom();
b=$urandom();
test=a+b;
if (test==out)
begin
$display("test case 3 is passed");
end
@(posedge clk);
a=$urandom();
b=$urandom();
test=a+b;
if (test==out)
begin
$display("test case 4 is passed");
end
@(posedge clk);
a=$urandom();
b=$urandom();
test=a+b;
if (test==out)
begin
$display("test case 5 is passed");
end
@(posedge clk);
a=$urandom();
b=$urandom();
test=a+b;
if (test==out)
begin
$display("test case 6 is passed");
end
@(posedge clk);
a=$urandom();
b=$urandom();
test=a+b;
if (test==out)
begin
$display("test case 7 is passed");
end
repeat(20) @(posedge clk);



$finish;
end

endmodule
