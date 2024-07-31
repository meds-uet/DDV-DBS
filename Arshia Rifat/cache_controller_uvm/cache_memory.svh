module cache_memory (
    input logic clk,
    input logic [31:0] address,
    input logic write_enable,
    input logic [31:0] write_data,
    output logic [31:0] read_data
);

    logic [31:0] memory [256][4];  // 256 lines, 4 words per line (each word of 32-bit)

    logic [7:0] index;
    logic [1:0] word_offset;

    assign index = address[11:4];
    assign word_offset = address[3:2];

    always_ff @(posedge clk) begin
        if (write_enable)
            memory[index][word_offset] <= write_data;
        read_data <= memory[index][word_offset];
    end

endmodule