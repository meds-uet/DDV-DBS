module FIFO #(
    parameter WIDTH = 16,
    parameter DEPTH = 16
)(
    input logic clk,
    input logic reset,
    input logic [WIDTH-1:0] data_in,
    input logic wr_en,
    input logic rd_en,
    output logic [WIDTH-1:0] data_out,
    output logic full,
    output logic empty
);

    logic [WIDTH-1:0] mem [DEPTH-1:0];
    logic [2:0] wr_pointer, rd_pointer, count;

    assign full = ( count == DEPTH);
    assign empty = (count == 0);
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            wr_pointer <= 0;
            rd_pointer <= 0;
            count <= 0;
           
        end else begin
            if (wr_en && !full) begin
                mem[wr_pointer] <= data_in;
                wr_pointer <= wr_pointer + 1;
                count <= count + 1;
            end
            if (rd_en && !empty) begin
                data_out <= mem[rd_pointer];
                rd_pointer <= rd_pointer + 1;
                count <= count - 1;
            end
        end
    end
endmodule