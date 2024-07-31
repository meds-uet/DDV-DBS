`timescale 1ns / 1ps

module top_module (
    input logic clk,
    input logic reset,
    input logic CPU_request,
    input logic [31:0] address,
    input logic [31:0] data_in,
    input logic read_req,
    input logic write_req,
    output logic [31:0] data_out
);

    logic Cache_hit, Cache_miss, Dirty_bit, Main_mem_ack, Flush_done;
    logic Cache_flush, Flush, Main_mem_access, mem_read_req, mem_write_req;
    logic [31:0] mem_data_out, mem_data_in;

    cache_controller cache_ctrl (
        .clk(clk),
        .reset(reset),
        .CPU_request(CPU_request),
        .Cache_hit(Cache_hit),
        .Cache_miss(Cache_miss),
        .Dirty_bit(Dirty_bit),
        .Main_mem_ack(Main_mem_ack),
        .Flush_done(Flush_done),
        .Cache_flush(Cache_flush),
        .Flush(Flush),
        .Main_mem_access(Main_mem_access),
        .mem_read_req(mem_read_req),
        .mem_write_req(mem_write_req),
        .state()
    );

    cache_mem cache (
        .clk(clk),
        .reset(reset),
        .CPU_request(CPU_request),
        .Cache_hit(Cache_hit),
        .Cache_miss(Cache_miss),
        .Dirty_bit(Dirty_bit),
        .Main_mem_ack(Main_mem_ack),
        .Flush_done(Flush_done),
        .Cache_flush(Cache_flush),
        .Flush(Flush),
        .Main_mem_access(Main_mem_access),
        .data_out(data_out),
        .mem_data_out(mem_data_out),
        .mem_read_req(mem_read_req),
        .mem_write_req(mem_write_req),
        .address(address),
        .data_in(data_in),
        .read_req(read_req),
        .write_req(write_req)
    );

    main_memory main_mem (
        .clk(clk),
        .reset(reset),
        .mem_read_req(mem_read_req),
        .mem_write_req(mem_write_req),
        .mem_data_in(data_out),
        .mem_data_out(mem_data_out),
        .mem_ack(Main_mem_ack),
        .address(address)
    );

endmodule
