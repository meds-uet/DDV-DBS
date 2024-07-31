`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/09/2024 02:20:51 PM
// Design Name: 
// Module Name: adder_tb
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




module adder_tb;

    parameter WIDTH = 4;
    logic [WIDTH-1:0] a1, b1;
    logic [WIDTH:0] x1;
    
    adder DUT (.a(a1), .b(b1), .x(x1));
    localparam period = 10;
    integer i;

    initial begin
        // Test each combination of a1 and b1 from 0 to 15
        for (i = 0; i < 16; i++) begin
            a1 = i;
            b1 = i;
            #period;
        end
        $stop;
    end

endmodule
