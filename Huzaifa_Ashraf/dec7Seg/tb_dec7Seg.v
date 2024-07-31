`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06/27/2024 11:02:18 PM
// Design Name: 
// Module Name: tb_dec7Seg
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


module tb_dec7Seg;

reg [3:0] in;
wire [6:0] out;

integer i;

dec7Seg dec_inst0(.in(in), .out(out));

initial begin
    for (i = 0; i < 17; i=i+1) begin
        in = i;
        #5;
        $display("input = %b, output = %b", in, out);
    end
    $finish;
end

endmodule