`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/02/2024 01:57:48 PM
// Design Name: 
// Module Name: shift_reg tb
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


module shift_regtb;
    logic clk;
    logic reset;
    logic in;
    logic [3:0] out;

    shif_register uut (
        .clk(clk),
        .reset(reset),
        .in(in),
        .out(out)
    );

    initial begin
        clk = 0;
        forever #5 clk = ~clk; // Generate clock with period 10
    end

    initial begin
        reset = 1; in = 0;
        #10 reset = 0; // Deassert reset
        #10 in = 1;
        #10 in = 0;
        #10 in = 1;
        #10 in = 1;
        #10 reset = 1; // Assert reset
        #10 reset = 0; // Deassert reset
        #10 in = 0;
        #10 $stop;
    end
endmodule
