`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/28/2024 07:41:28 AM
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

parameter WIDTH=8;

reg clk, reset, up_or_down;
reg [WIDTH-1:0]init_val;
wire [WIDTH-1:0]out;


//instantiation...
counter DUT(.reset(reset),.clk(clk),.up_or_down(up_or_down),.init_val(init_val),.out(out));


initial begin

clk = 0; reset = 0; init_val = 8'b00000000; up_or_down = 1;// reset at the very start stage...
#10;
clk = 1; reset = 1; 
#10;
clk = 0; reset = 1;
#10;
clk = 1; reset = 1;
#10;
clk = 0; reset = 1;
#10;
clk = 1; reset = 1;
#10;
clk = 0; reset = 1;
#10;
clk = 1; reset = 1;
#10;
clk = 0; reset = 1;
#10;
clk = 1; reset = 1;
#10;
clk = 0; reset = 1;
#10;
clk = 1; reset = 1;
#10;
clk = 0; reset = 1;
#10;
clk = 1; reset = 0; init_val = out; up_or_down = 0; // reset again and start down counting...
#10;
clk = 0; reset = 1;
#10;
clk = 1; reset = 1;
#10;
clk = 0; reset = 1;
#10;
clk = 1; reset = 1;
#10;
clk = 0; reset = 1;
#10;
clk = 1; reset = 1;
#10;
clk = 0; reset = 1;
#10;
clk = 1; reset = 1;
#10;
clk = 0; reset = 1;
#10;
clk = 1; reset = 1;
#10;
clk = 0; reset = 1;
#10;
clk = 1; reset = 1;
#10;
$stop;

end

endmodule
