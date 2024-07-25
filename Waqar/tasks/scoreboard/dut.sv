module dut (
  input logic clk,
  input logic reset,
  input logic [7:0] data_in,
  output logic [7:0] data_out,
  input logic mode // 0: pass-through, 1: invert data
);

  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      data_out <= 8'h00;
    end else begin
      if (mode == 0) begin
        data_out <= data_in;
      end else begin
        data_out <= ~data_in;
      end
    end
  end

endmodule
