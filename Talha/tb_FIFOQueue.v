`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.07.2024 20:54:38
// Design Name: 
// Module Name: tb_FIFOQueue
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



module tb_FIFOQueue;
    parameter DATA_WIDTH = 8;
    parameter DEPTH = 16;

    reg clk;
    reg rst;
    reg enq;
    reg deq;
    reg [DATA_WIDTH-1:0] din;
    wire [DATA_WIDTH-1:0] dout;
    wire full;
    wire empty;

    // Instantiate the FIFOQueue
    FIFOQueue #(DATA_WIDTH, DEPTH) uut (
        .clk(clk),
        .rst(rst),
        .enq(enq),
        .deq(deq),
        .din(din),
        .dout(dout),
        .full(full),
        .empty(empty)
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
        enq = 0;
        deq = 0;
        din = 0;

        // Apply reset
        rst = 1;
        #10;
        rst = 0;
        #10;

        // Test enqueue operations
        enq = 1;
        din = 8'h01; #10;
        din = 8'h02; #10;
        din = 8'h03; #10;
        enq = 0;

        // Test dequeue operations
        #10;
        deq = 1; #10;
        deq = 0;

        // Test enqueue and dequeue together
        enq = 1;
        din = 8'h04; #10;
        deq = 1; #10;
        enq = 0;
        deq = 0;

        // Fill the FIFO to test the full flag
        enq = 1;
        din = 8'h05; #10;
        din = 8'h06; #10;
        din = 8'h07; #10;
        din = 8'h08; #10;
        din = 8'h09; #10;
        din = 8'h0A; #10;
        din = 8'h0B; #10;
        din = 8'h0C; #10;
        din = 8'h0D; #10;
        din = 8'h0E; #10;
        din = 8'h0F; #10;
        din = 8'h10; #10;
        enq = 0;

        // Empty the FIFO to test the empty flag
        deq = 1; #10;
        deq = 0; #10;
        deq = 1; #10;
        deq = 0; #10;
        deq = 1; #10;
        deq = 0; #10;
        deq = 1; #10;
        deq = 0; #10;
        deq = 1; #10;
        deq = 0; #10;
        deq = 1; #10;
        deq = 0; #10;
        deq = 1; #10;
        deq = 0; #10;
        deq = 1; #10;
        deq = 0; #10;
        deq = 1; #10;
        deq = 0; #10;
        deq = 1; #10;
        deq = 0; #10;
        deq = 1; #10;
        deq = 0; #10;

        $finish;  // End the simulation
    end

    // Monitor the FIFO queue state
    initial begin
        $monitor("Time=%0t, dout=%h, full=%b, empty=%b", $time, dout, full, empty);
    end

endmodule

