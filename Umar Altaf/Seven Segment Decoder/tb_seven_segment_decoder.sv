`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 01:34:42 PM
// Design Name: 
// Module Name: tb_seven_segment_decoder
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


module tb_seven_segment_decoder;
reg clk;
reg [3:0]in;
reg [6:0]out;
reg [6:0]result;
seven_segment_decoder sd(in,out);
initial begin 
   clk = 0;
  forever 
     #5 clk = ~clk;
end
initial
begin
$monitor("in = %b,out = %b,result = %b", in, out, result);
 end
initial
begin



@(posedge clk); 
@(posedge clk);  


in=$urandom();
@(posedge clk); 
@(posedge clk);  
task1(in);  
@(posedge clk);  
@(posedge clk);
if (result!=out)
begin
$display( "The result case 1 is incorrect");
end
in=$urandom();
@(posedge clk);  
@(posedge clk);
task1(in);  
@(posedge clk);  
@(posedge clk);  


if (result!=out)
$display( "The result case 2 is incorrect");


@(posedge clk); 
 
in=$urandom();

@(posedge clk);  
@(posedge clk);
task1(in);   
 @(posedge clk);  
@(posedge clk);
if (result!=out)
$display( "The result case 3 is incorrect");
@(posedge clk);  

repeat(20) @(posedge clk);


 
$finish;

end
task task1(input [3:0]in);
case(in)
4'b0000 : result=7'b1111110;
4'b0001 : result=7'b0110000;
4'b0010 : result=7'b1101101;     
4'b0011 : result=7'b1111001;
4'b0100 : result=7'b0110011;
4'b0101 : result=7'b1011011;
4'b0110 : result=7'b1011111;
4'b0111 : result=7'b1110000;
4'b1000 : result=7'b1111111;
4'b1001 : result=7'b1111011;
4'b1010 : result=7'b1110111;
4'b1011 : result=7'b0011111;
4'b1100 : result=7'b1001110;
4'b1101 : result=7'b0111101;
4'b1110 : result=7'b1001111;
4'b1111 : result=7'b1000111;
default:result=7'b1111110;

endcase
endtask





endmodule
