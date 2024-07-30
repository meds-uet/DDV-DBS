module FIFO #(parameter DATA_WIDTH = 8, parameter DEPTH = 16) (
  input logic clk,
  input logic rst,
  input logic wr_en,
  input logic rd_en,
  input logic [DATA_WIDTH-1:0] wr_data,
  output logic [DATA_WIDTH-1:0] rd_data,
  output logic empty,
  output logic full
);

  logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];
  logic [$clog2(DEPTH):0] wr_ptr, rd_ptr, count;

  assign empty = (count == 0);
  assign full = (count == DEPTH);

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      wr_ptr <= 0;
      rd_ptr <= 0;
      count <= 0;
    end else begin
      if (wr_en && !full) begin
        mem[wr_ptr] <= wr_data;
        wr_ptr <= wr_ptr + 1;
        count <= count + 1;
      end
      if (rd_en && !empty) begin
        rd_data <= mem[rd_ptr];
        rd_ptr <= rd_ptr + 1;
        count <= count - 1;
      end
    end
  end
endmodule