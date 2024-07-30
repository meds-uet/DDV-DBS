`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/08/2024 03:24:42 PM
// Design Name: 
// Module Name: Testbench
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

module tb_fifo_queue();

    parameter DATA_WIDTH = 8;
    parameter DEPTH = 16;

    logic clk;
    logic reset;
    logic enq;
    logic deq;
    logic [DATA_WIDTH-1:0] data_in;
    logic [DATA_WIDTH-1:0] data_out;
    logic full;
    logic empty;

    // Instantiate the FIFO queue
    fifo_queue #(
        .DATA_WIDTH(DATA_WIDTH),
        .DEPTH(DEPTH)
    ) uut (
        .clk(clk),
        .reset(reset),
        .enq(enq),
        .deq(deq),
        .data_in(data_in),
        .data_out(data_out),
        .full(full),
        .empty(empty)
    );

    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    initial begin
        reset = 1;
        enq = 0;
        deq = 0;
        data_in = 0;

        #10 reset = 0;

        enqueue_test();
        dequeue_test();
        random_test();

        $stop;
    end

    // Task to perform enqueue operations
    task enqueue_test();
        begin
            $display("Testing enqueue operations...");
            for (int i = 0; i < DEPTH; i = i + 1) begin
                @(posedge clk);
                enq = 1;
                data_in = i;
                @(posedge clk);
                enq = 0;
                monitor_fifo_status();
            end
            monitor_fifo_status();
        end
    endtask

    // Task to perform dequeue operations
    task dequeue_test();
        begin
            $display("Testing dequeue operations...");
            for (int i = 0; i < DEPTH; i = i + 1) begin
                @(posedge clk);
                deq = 1;
                @(posedge clk);
                deq = 0;
                monitor_fifo_status();
            end
            monitor_fifo_status();
        end
    endtask

    // Task to perform random enqueue and dequeue operations
    task random_test();
        begin
            $display("Testing random enqueue and dequeue operations...");
            for (int i = 0; i < DEPTH*2; i = i + 1) begin
                @(posedge clk);
                enq = $urandom_range(0, 1);
                deq = $urandom_range(0, 1);
                if (enq && !full) data_in = $urandom_range(0, 2**DATA_WIDTH-1);
                @(posedge clk);
                enq = 0;
                deq = 0;
                monitor_fifo_status();
            end
        end
    endtask

    // Task to monitor the FIFO status
    task monitor_fifo_status();
        begin
            if (full) $display("Queue is full.");
            if (empty) $display("Queue is empty.");
        end
    endtask

endmodule
