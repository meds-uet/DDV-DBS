module FIFO #(parameter DATA_WIDTH = 8, parameter DEPTH = 16) (
  input logic clock,
  input logic reset,
  input logic write_enable,
  input logic read_enable,
  input logic [DATA_WIDTH-1:0] write_data,
  output logic [DATA_WIDTH-1:0] read_data,
  output logic fifo_empty,
  output logic fifo_full
);

  logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];
  logic [$clog2(DEPTH):0] wr_ptr, rd_ptr, count;

  assign fifo_empty = (count == 0);
  assign fifo_full = (count == DEPTH);

  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      wr_ptr <= 0;
      rd_ptr <= 0;
      count <= 0;
    end else begin
      if (write_enable && !fifo_full) begin
        mem[wr_ptr] <= write_data;
        wr_ptr <= wr_ptr + 1;
        count <= count + 1;
      end
      if (read_enable && !fifo_empty) begin
        read_data <= mem[rd_ptr];
        rd_ptr <= rd_ptr + 1;
        count <= count - 1;
      end
    end
  end
endmodule