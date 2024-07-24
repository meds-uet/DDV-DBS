`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/10/2024 02:58:24 PM
// Design Name: 
// Module Name: ffqueuetb
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


module ffqueuetb;

    parameter DEPTH = 8;
    parameter WIDTH = 8;

    logic clk;
    logic rst;
    logic enq;
    logic deq;
    logic [WIDTH-1:0] data_in;
    logic [WIDTH-1:0] data_out;
    logic full;
    logic empty;

    fifo_queue #(.DEPTH(DEPTH), .WIDTH(WIDTH)) uut (
        .clk(clk),
        .rst(rst),
        .enq(enq),
        .deq(deq),
        .data_in(data_in),
        .data_out(data_out),
        .full(full),
        .empty(empty)
    );

    // Clock generation
    always #5 clk = ~clk;

    // Test vectors
    initial begin
        // Initialize signals
        clk = 0;
        rst = 1;
        enq = 0;
        deq = 0;
        data_in = 0;

        // Reset the FIFO
        #10;
        rst = 0;

        // Test case 1: Enqueue and Dequeue
        enq = 1;
        for (int i = 0; i < DEPTH; i++) begin
            data_in = i;
            #10;
        end
        enq = 0;

        // Check if FIFO is full
        if (full)
            $display("FIFO is full as expected.");

        // Dequeue all elements
        deq = 1;
        for (int i = 0; i < DEPTH; i++) begin
            #10;
            $display("Dequeued data: %d", data_out);
        end
        deq = 0;

        // Check if FIFO is empty
        if (empty)
            $display("FIFO is empty as expected.");

        // Test case 2: Enqueue and Dequeue in interleaved manner
        enq = 1;
        deq = 1;
        for (int i = 0; i < 2 * DEPTH; i++) begin
            data_in = i;
            #10;
            $display("Data in: %d, Data out: %d", data_in, data_out);
        end
        enq = 0;
        deq = 0;

        // Check if FIFO is empty again
        if (empty)
            $display("FIFO is empty after interleaved operations as expected.");

        $stop;
    end
endmodule

