`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/18/2024 12:50:13 PM
// Design Name: 
// Module Name: scoreboard_tb
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

`include "scoreboard.sv"

module tb_scoreboard;
    // DUT signals
    logic clk, reset;
    logic [7:0] data_in, data_out;

    // Instantiate DUT
    queue uut (
        .clk(clk),
        .reset(reset),
        .data_in(data_in),
        .data_out(data_out)
    );

    // Instantiate Scoreboard
    Scoreboard #(.DATA_WIDTH(8)) scoreboard;

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Test stimulus and scoreboard usage
    initial begin
        // Initialize
        scoreboard = new();
        reset = 1;
        data_in = 8'h01;
        @(posedge clk);
        reset = 0;

        // Test case 1: Simple data pass-through
        data_in = 8'hAA;
        scoreboard.add_expected(data_in);
        @(posedge clk);

        // Compare result
        scoreboard.compare_result(data_out);

        // Test case 2: Data inversion (assuming DUT inverts data)
        data_in = 8'h55;
        scoreboard.add_expected(~data_in);
        @(posedge clk);

        // Compare result
        scoreboard.compare_result(data_out);

        // Add more test cases here...

        // Report scoreboard statistics
        scoreboard.report_statistics();

      //  $finish;
    end
endmodule

