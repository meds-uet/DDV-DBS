module CacheMem (
    input logic clk,
    input logic [31:0] address,
    input logic write_enable,
    input logic [31:0] write_data,
    output logic [31:0] read_data
);

    // cache memory array (256 lines, 4 words/line)
    logic [31:0] memory [256][4];

    // Index for the cache line + word offset within the line
    logic [7:0] index;
    logic [1:0] word_offset;

    // extracting index and word offset from the address
    assign index = address[11:4];
    assign word_offset = address[3:2];

    // Sequential logic block triggered on the clock's positive edge
    always_ff @(posedge clk) begin
        if (write_enable) begin
            // Write data to the cache
            memory[index][word_offset] <= write_data;
        end
        // Read data from the cache
        read_data <= memory[index][word_offset];
    end

endmodule
