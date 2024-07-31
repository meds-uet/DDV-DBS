module dut (
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  data_in,
  output logic [7:0]  data_out
);

  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      data_out <= 8'h00;
    end else begin
      data_out <= ~data_in; // Inverting the data
    end
  end

endmodule
