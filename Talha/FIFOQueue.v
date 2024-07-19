`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.07.2024 20:53:01
// Design Name: 
// Module Name: FIFOQueue #
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


module FIFOQueue #(
    parameter DATA_WIDTH = 8,  // Width of the data
    parameter DEPTH = 16       // Depth of the FIFO queue
)(
    input wire clk,                    // Clock signal
    input wire rst,                    // Reset signal
    input wire enq,                    // Enqueue control signal
    input wire deq,                    // Dequeue control signal
    input wire [DATA_WIDTH-1:0] din,   // Data input
    output reg [DATA_WIDTH-1:0] dout,  // Data output
    output reg full,                   // Full flag
    output reg empty                   // Empty flag
);

    reg [DATA_WIDTH-1:0] fifo_mem [0:DEPTH-1]; // FIFO memory array
    reg [31:0] write_ptr;                      // Write pointer
    reg [31:0] read_ptr;                       // Read pointer
    reg [31:0] count;                          // Count of elements in FIFO

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            write_ptr <= 0;
            read_ptr <= 0;
            count <= 0;
            full <= 0;
            empty <= 1;
        end else begin
            if (enq && !full) begin
                fifo_mem[write_ptr] <= din;
                write_ptr <= (write_ptr + 1) % DEPTH;
                count <= count + 1;
            end
            if (deq && !empty) begin
                dout <= fifo_mem[read_ptr];
                read_ptr <= (read_ptr + 1) % DEPTH;
                count <= count - 1;
            end

            // Update full and empty flags
            full <= (count == DEPTH);
            empty <= (count == 0);
        end
    end

endmodule
