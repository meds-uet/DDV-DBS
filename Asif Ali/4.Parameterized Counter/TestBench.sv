`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/08/2024 03:00:00 PM
// Design Name: 
// Module Name: Parameterized_Counter_tb
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: Testbench for Parameterized Counter to verify up, down, and reset operations.
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

module Parameterized_Counter_tb;
    // Parameters
    localparam int WIDTH = 8;

    // Inputs
    logic clk;
    logic rst_n;
    logic up;
    logic down;
    logic [WIDTH-1:0] initial_value;

    // Outputs
    logic [WIDTH-1:0] count;

    Parameterized_Counter #(
        .WIDTH(WIDTH)
    ) uut (
        .clk(clk),
        .rst_n(rst_n),
        .up(up),
        .down(down),
        .initial_value(initial_value),
        .count(count)
    );

    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 10 ns period
    end

    initial begin
        // Initialize Inputs
        rst_n = 0;
        up = 0;
        down = 0;
        initial_value = 8'h00;

        // Apply Reset
        #10;
        rst_n = 1;
        #10;
        assert(count == initial_value) 
            else $fatal("Test 1 failed: Count not equal to initial value after reset.");

        // Test 2: Counting Up from initial value
        initial_value = 8'h10;
        rst_n = 0;
        #10;
        rst_n = 1;
        #10;
        up = 1;
        #50;  
        up = 0;
        #10;
        assert(count == 8'h10 + 5) 
            else $fatal("Test 2 failed: Count not as expected after counting up.");

        // Test 3: Counting Down from current value
        down = 1;
        #30;  // Counting down for soome time
        down = 0;
        #10;
        assert(count == 8'h10 + 5 - 3) 
            else $fatal("Test 3 failed: Count not as expected after counting down.");

        // Test 4: Reset with a different initial value
        rst_n = 0;
        initial_value = 8'hAA;
        #10;
        rst_n = 1;
        #10;
        assert(count == initial_value) 
            else $fatal("Test 4 failed: Count not equal to new initial value after reset.");

        // Test 5: Check boundary conditions
        initial_value = 8'hFE;
        rst_n = 0;
        #10;
        rst_n = 1;
        #10;
        up = 1;
        #10; // Increment once
        up = 0;
        #10;
        assert(count == 8'hFF) 
            else $fatal("Test 5 failed: Count not as expected at boundary after counting up.");

        // Test 6: Counting down from zero
        initial_value = 8'h00;
        rst_n = 0;
        #10;
        rst_n = 1;
        #10;
        down = 1;
        #10;  //Wating to complete the cycle
        down = 0;
        #10;
        assert(count == 8'h00) 
            else $fatal("Test 6 failed: Count went below zero after decrementing from zero.");

        // Test 7: Verify counting down multiple times
        initial_value = 8'h10;
        rst_n = 0;
        #10;
        rst_n = 1;
        #10;
        down = 1;
        #40;  // Allow time for multiple decrements
        down = 0;
        #10;
        assert(count == 8'h10 - 4) 
            else $fatal("Test 7 failed: Count not as expected after multiple decrements.");

        // Test 8: Reset and then decrement from zero
        rst_n = 0;
        #10;
        rst_n = 1;
        initial_value = 8'h00;
        #10;
        down = 1;
        #10;  
        down = 0;
        #10;
        assert(count == 8'h00) 
            else $fatal("Test 8 failed: Count changed unexpectedly after reset and decrement.");

        // Test 9: Counting down with non-zero initial value and reset
        initial_value = 8'h05;
        rst_n = 0;
        #10;
        rst_n = 1;
        #10;
        down = 1;
        #20;
        down = 0;
        #10;
        assert(count == 8'h05 - 2) 
            else $fatal("Test 9 failed: Count not as expected after counting down from a non-zero value.");

        // Finish the simulation
        $finish;
    end

endmodule
