module alu_design(
  input logic [15:0] a,
  input logic [15:0] b,
  input logic [2:0] sel,
  output logic [15:0] out
);
  always_comb begin
    case (sel)
      3'b000 : out = a + b;   // Addition
      3'b001 : out = a - b;   // Subtraction
      3'b010 : out = a & b;   // Bitwise AND
      3'b011 : out = a | b;   // Bitwise OR
      3'b100 : out = a ^ b;   // Bitwise XOR
      default: out = 16'h0000; // Default case
    endcase
  end
endmodule