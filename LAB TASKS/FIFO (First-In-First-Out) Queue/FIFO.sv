`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/16/2024 05:08:16 PM
// Design Name: 
// Module Name: FIFO
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

module FIFO #(
    parameter WIDTH = 8,    // Data width
    parameter DEPTH = 8     // FIFO depth
)
(
    input logic clk,         // Clock signal
    input logic reset,       // Reset signal
    input logic enq,         // Enqueue signal
    input logic deq,         // Dequeue signal
    input logic [WIDTH-1:0] data_in,   // Data input
    output logic [WIDTH-1:0] data_out, // Data output
    output logic empty,      // Empty flag
    output logic full        // Full flag
);

// Memory array to store the data
logic [WIDTH-1:0] mem [0:DEPTH-1];
// Write and read pointers
logic [$clog2(DEPTH)-1:0] write_ptr, read_ptr;
// Counter to keep track of the number of elements in the FIFO
logic [$clog2(DEPTH):0] counter;

// Initialize the memory with 'x'
integer i;
initial begin
    for (i = 0; i < DEPTH; i++) begin
        mem[i] = 8'hxx;
    end
end

// Always block triggered on the rising edge of the clock or the reset signal
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        write_ptr <= 0;
        read_ptr <= 0;
        counter <= 0;
    end else begin
        if (enq && !full) begin
            mem[write_ptr] <= data_in;
            write_ptr <= write_ptr + 1;
            counter <= counter + 1;
        end
        if (deq && !empty) begin
            data_out <= mem[read_ptr];
            read_ptr <= read_ptr + 1;
            counter <= counter - 1;
        end
    end
end

// Assign the full and empty flags
assign full = (counter == DEPTH);
assign empty = (counter == 0);

endmodule

