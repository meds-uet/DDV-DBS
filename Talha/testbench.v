`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.07.2024 20:47:17
// Design Name: 
// Module Name: testbench
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



module testbench;
    parameter WIDTH = 8;  // Specify the width of the counter for the testbench
    reg clk;              // Clock signal
    reg rst;              // Reset signal
    reg up;               // Up control signal
    reg down;             // Down control signal
    reg [WIDTH-1:0] initial_value; // Initial value input
    wire [WIDTH-1:0] count;        // Counter output

    // Instantiate the parameterized counter
    paramCounter #(WIDTH) uut (
        .clk(clk),
        .rst(rst),
        .up(up),
        .down(down),
        .initial_value(initial_value),
        .count(count)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 10 time units clock period
    end

    // Test sequence
    initial begin
        // Initialize signals
        rst = 0;
        up = 0;
        down = 0;
        initial_value = 8'h0;

        // Apply reset and set initial value to 8
        rst = 1;
        initial_value = 8'h08;
        #10;
        rst = 0;
        #10;

        // Test up count
        up = 1;
        #50;
        up = 0;
        #10;

        // Test down count
        down = 1;
        #50;
        down = 0;
        #10;

        // Apply reset again and set initial value to 16
        rst = 1;
        initial_value = 8'h10;
        #10;
        rst = 0;
        #10;

        // Test up count again
        up = 1;
        #50;
        up = 0;
        #10;

        // Test down count again
        down = 1;
        #50;
        down = 0;
        #10;

        $finish;  // End the simulation
    end

    // Monitor the counter value
    initial begin
        $monitor("Time=%0t, count=%d, up=%b, down=%b, rst=%b, initial_value=%d", $time, count, up, down, rst, initial_value);
    end

endmodule
