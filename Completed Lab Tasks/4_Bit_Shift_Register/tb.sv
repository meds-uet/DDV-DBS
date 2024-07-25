`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/02/2024 12:58:43 PM
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
logic clk,reset;
logic d;
logic [3:0] q;
Shift_register DUT (.clk(clk),.reset(reset),.serial_in(d),.parallel_out(q));



initial begin
reset=1;
#5
reset=0;
#10
reset=1;
#5
reset=0;

end

initial begin
clk=0;
forever #5 clk=~clk;
end

initial begin

d=0;
#5

d=1;
#10

d=0;
#5

d=1;
#10

d=0;
#5

d=1;
#10

d=0;
#5

d=1;
#10

$stop;
end
endmodule
