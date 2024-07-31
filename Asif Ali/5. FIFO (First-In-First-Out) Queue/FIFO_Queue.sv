module fifo_queue #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 16
) (
    input logic clk,
    input logic reset,
    input logic enq,  
    input logic deq,  
    input logic [DATA_WIDTH-1:0] data_in,  
    output logic [DATA_WIDTH-1:0] data_out,  
    output logic full,  
    output logic empty  
);

    // Internal signals
    logic [DATA_WIDTH-1:0] fifo_mem [0:DEPTH-1];
    logic [$clog2(DEPTH):0] write_ptr;
    logic [$clog2(DEPTH):0] read_ptr;
    logic [$clog2(DEPTH+1):0] fifo_count;

    // Full and empty signals
    assign full = (fifo_count == DEPTH);
    assign empty = (fifo_count == 0);

    // Enqueue operation
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            write_ptr <= 0;
            fifo_count <= 0;
        end else if (enq && !full) begin
            fifo_mem[write_ptr] <= data_in;
            write_ptr <= (write_ptr + 1) % DEPTH;
            fifo_count <= fifo_count + 1;
        end
    end

    // Dequeue operation
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            read_ptr <= 0;
            fifo_count <= 0;
            data_out <= 0;
        end else if (deq && !empty) begin
            data_out <= fifo_mem[read_ptr];
            read_ptr <= (read_ptr + 1) % DEPTH;
            fifo_count <= fifo_count - 1;
        end
    end

endmodule
