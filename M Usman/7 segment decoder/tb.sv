`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/04/2024 12:26:43 AM
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


reg [3:0]in;
wire [6:0]out;

task testcase();

in = 4'b0000;
#10;
in = 4'b0001;
#10;
in = 4'b0010;
#10;
in = 4'b0011;
#10;
in = 4'b0100;
#10;
in = 4'b0101;
#10;
in = 4'b0110;
#10;
in = 4'b0111;
#10;
in = 4'b1000;
#10;
in = 4'b1001;
#10;
in = 4'b1010;
#10;
in = 4'b1011;
#10;
in = 4'b1100;
#10;
in = 4'b1101;
#10;
in = 4'b1110;
#10;
in = 4'b1111;
#10;

endtask

decoder DUT(.in(in),.out(out));


initial begin

testcase();

$stop;
end

endmodule
