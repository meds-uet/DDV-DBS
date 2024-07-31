module SISO(
  input wire clk,
  input wire clear,
  input wire A,
  output reg E
);

// Intermediate registers
reg B, C, D;

always @(posedge clk or negedge clear) begin
  if (!clear) begin
    B <= 0;
    C <= 0;
    D <= 0;
    E <= 0;
  end else begin
    E <= D;
    D <= C;
    C <= B;
    B <= A;
  end
end

endmodule


