`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/11/2024 09:53:40 AM
// Design Name: 
// Module Name: Counter_tb
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


module Counter_tb;

parameter WIDTH = 3; // Parameter for width
logic clk1, reset1, enable1, count_up1; // Testbench signals
logic [WIDTH-1:0] init_value1, d1; // Signals for initial value and output

// Instantiate the DUT (Device Under Test)
Counter DUT (
    .clk(clk1),
    .reset(reset1),
    .enable(enable1),
    .count_up(count_up1),
    .init_value(init_value1),
    .d(d1)
);

// Clock generation
initial begin 
    clk1 = 0;
    forever #5 clk1 = ~clk1; // Toggle clock every 5 time units
end

// Reset signal generation
initial begin 
    reset1 = 1;
    #5;
    reset1 = 0;
end

// Stimulus process
initial begin
    reset1 = 1;
    enable1 = 0;
    init_value1 = 1;
    count_up1 = 0;
    #5;
    reset1 = 0;
    enable1 = 1;
    count_up1 = 1;
    #45;
    count_up1 = 0;
    #50;
    $stop;
end

endmodule
