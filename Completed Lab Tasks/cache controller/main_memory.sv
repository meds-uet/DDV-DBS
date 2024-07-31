`timescale 1ns / 1ps

module main_memory (
    input logic clk,
    input logic reset,
    input logic mem_read_req,
    input logic mem_write_req,
    input logic [31:0] mem_data_in,
    output logic [31:0] mem_data_out,
    output logic mem_ack,
    input logic [31:0] address
);

    parameter MEM_SIZE = 8;
    localparam INDEX_WIDTH = $clog2(MEM_SIZE);

    logic [31:0] memory [0:MEM_SIZE-1];
    logic [INDEX_WIDTH-1:0] index;
    integer i;

    assign index = address[INDEX_WIDTH+1:2];

    always_ff @(posedge clk or negedge reset) begin
        if (!reset) begin
            for (i = 0; i < MEM_SIZE; i++) begin
                memory[i] <= i;
            end
            mem_data_out <= 32'h0;
            mem_ack <= 1'b0;
        end else begin
            if (mem_read_req) begin
                mem_data_out <= memory[index];
                mem_ack <= 1'b1;
            end else if (mem_write_req) begin
                memory[index] <= mem_data_in;
                mem_ack <= 1'b1;
            end else begin
                mem_ack <= 1'b0;
            end
        end
    end

endmodule
