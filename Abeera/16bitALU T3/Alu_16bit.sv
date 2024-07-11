module Alu_16bit(
    input logic [15:0] a,
    input logic [15:0] b,
    input logic [2:0] sig,
    output logic [15:0] out
);

always @(*) begin
case(sig)
3'b001: out = a + b;
3'b010: out = a -b;
3'b011: out = a & b;
3'b100: out = a | b;
3'b101: out = a ^ b;
default: out = 16'b0; //handle cases like 000,111,110
endcase
end
endmodule 
