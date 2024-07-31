`timescale 1ns / 1ps

module cache_mem (
    input logic clk,
    input logic reset,
    input logic CPU_request,
    input logic read_req,
    input logic write_req,
    input logic [31:0] address,
    input logic [31:0] data_in,
    output logic [31:0] data_out,
    output logic Cache_hit,
    output logic Cache_miss,
    output logic Dirty_bit,
    input logic Main_mem_ack,
    input logic Flush_done,
    output logic Cache_flush,
    output logic Flush,
    output logic Main_mem_access,
    input logic [31:0] mem_data_out,
    output logic mem_read_req,
    output logic mem_write_req
);

    parameter NUM_SETS = 8;
    localparam INDEX_WIDTH = $clog2(NUM_SETS);

    typedef struct {
        logic valid;
        logic dirty;
        logic [31-INDEX_WIDTH-2:0] tag;
        logic [31:0] data;
    } cache_line;

    cache_line cache[0:NUM_SETS-1];
    logic [INDEX_WIDTH-1:0] index;
    logic [31-INDEX_WIDTH-2:0] tag_bits;
    integer i;

    assign index = address[INDEX_WIDTH + 1:2];
    assign tag_bits = address[31:INDEX_WIDTH+2];

    assign Cache_hit = (cache[index].valid || (cache[index].tag == tag_bits));
    assign Cache_miss = !Cache_hit;
    assign Dirty_bit = (Cache_hit) ? cache[index].dirty : 1'b0;
    assign mem_read_req = (Cache_miss && !Dirty_bit);
    assign mem_write_req = (Cache_miss && Dirty_bit);

    always_ff @(posedge clk or negedge reset) begin
        if (!reset) begin
            for (i = 0; i < NUM_SETS; i++) begin
                cache[i].valid <= 1'b0;
                cache[i].tag <= 0;
                cache[i].data <= 32'h0;
                cache[i].dirty <= 1'b0;
            end
        end else begin
            if (Cache_miss) begin
                if (Dirty_bit) begin
                    mem_write_req <= 1'b1;
                    data_out <= cache[index].data;
                end else begin
                    mem_read_req <= 1'b1;
                end
            end else begin
                mem_read_req <= 1'b0;
                mem_write_req <= 1'b0;
            end

            if (write_req && !Cache_miss) begin
                cache[index].valid <= 1'b1;
                cache[index].tag <= tag_bits;
                cache[index].data <= data_in;
                cache[index].dirty <= 1'b1;
            end
            
            if (read_req && Cache_hit) begin
                data_out <= cache[index].data;
            end
            
            if (mem_read_req && Main_mem_ack) begin
                cache[index].valid <= 1'b1;
                cache[index].tag <= tag_bits;
                cache[index].data <= mem_data_out;
                cache[index].dirty <= 1'b0;
            end

            if (Flush) begin
                cache[index].valid <= 1'b0;
                cache[index].tag <= 0;
                cache[index].data <= 32'h0;
                cache[index].dirty <= 1'b0;
            end
        end
    end

endmodule
