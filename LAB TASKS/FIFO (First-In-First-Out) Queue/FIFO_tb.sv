`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/16/2024 05:30:27 PM
// Design Name: 
// Module Name: FIFO_tb
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


module FIFO_tb;

parameter WIDTH = 8;  // Data width
parameter DEPTH = 8;  // FIFO depth

// Declare signals
logic clk, reset, enq1, deq1, empty1, full1;
logic [WIDTH-1:0] data_in1, data_out1;

// Instantiate the FIFO module
FIFO DUT (
    .clk(clk),
    .reset(reset),
    .enq(enq1),
    .deq(deq1),
    .empty(empty1),
    .full(full1),
    .data_in(data_in1),
    .data_out(data_out1)
);

// Generate clock signal
initial begin
    clk = 0;
    forever #5 clk = ~clk;
end

// Generate reset signal
initial begin
    reset = 1;
    #10 reset = 0;
end

// Test sequence
initial begin
    // Initialize signals
    enq1 = 0;
    deq1 = 0;
    data_in1 = 1;
    data_out1 = 1;

    // Apply reset
    reset = 1;
    #5;
    reset = 0;

    // Enqueue data into FIFO
    enq1 = 1;
    for (integer x = 0; x < DEPTH; x++) begin
        data_in1 = x;
        #10;
    end
    enq1 = 0;

    // Dequeue data from FIFO
    deq1 = 1;
    #100;
    deq1 = 0;

    // Stop the simulation
    $stop;
end

endmodule
