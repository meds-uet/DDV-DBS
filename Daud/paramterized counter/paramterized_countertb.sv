`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/24/2024 09:08:35 PM
// Design Name: 
// Module Name: paramterized_countertb
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


module tb_parameterized_counter;

    // Parameters
    localparam WIDTH = 8;  // Width of the counter
    localparam INIT_VAL = 8'h5A; // Initial value for the counter

    // Testbench signals
    logic clk;
    logic rst_n;
    logic up;
    logic down;
    logic [WIDTH-1:0] init_val;
    logic [WIDTH-1:0] count;

    // Instantiate the parameterized counter
    parameterized_counter #(
        .WIDTH(WIDTH)
    ) uut (
        .clk(clk),
        .rst_n(rst_n),
        .up(up),
        .down(down),
        .init_val(init_val),
        .count(count)
    );

    // Clock generation
    always begin
        #5 clk = ~clk;
    end

    // Test sequence
    initial begin
        // Initialize signals
        clk = 0;
        rst_n = 0;
        up = 0;
        down = 0;
        init_val = INIT_VAL;

        // Apply reset
        #10 rst_n = 1;

        // Test case 1: Count up
        #10 up = 1; down = 0;
        #20 up = 0;

        // Test case 2: Count down
        #10 down = 1; up = 0;
        #20 down = 0;

        // Test case 3: Reset with a different initial value
        #10 rst_n = 0; init_val = 8'h3C;
        #10 rst_n = 1;

        // Finish simulation
        #20 $finish;
    end

    // Monitor outputs
    initial begin
        $monitor("Time = %0t, count = %0h", $time, count);
    end

endmodule

