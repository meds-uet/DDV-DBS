module fifo_queue #(parameter DEPTH = 16, DATA_WIDTH = 8) (
    input logic clk,
    input logic reset,
    input logic enq,        // Enqueue operation
    input logic deq,        // Dequeue operation
    input logic [DATA_WIDTH-1:0] data_in,  // Data to enqueue
    output logic [DATA_WIDTH-1:0] data_out, // Data to dequeue
    output logic full,      // FIFO is full
    output logic empty      // FIFO is empty
);

    logic [DATA_WIDTH-1:0] queue [0:DEPTH-1]; // FIFO storage
    logic [$clog2(DEPTH):0] read_ptr, write_ptr; // Read and write pointers
    logic [$clog2(DEPTH+1)-1:0] count; // Number of elements in the queue

    // Assign output signals
    assign full = (count == DEPTH);
    assign empty = (count == 0);

    // Enqueue operation
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            write_ptr <= 0;
            count <= 0;
        end else if (enq && !full) begin
            queue[write_ptr] <= data_in;
            write_ptr <= write_ptr + 1;
            count <= count + 1;
        end
    end

    // Dequeue operation
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            read_ptr <= 0;
            count <= 0;
        end else if (deq && !empty) begin
            data_out <= queue[read_ptr];
            read_ptr <= read_ptr + 1;
            count <= count - 1;
        end
    end

endmodule
