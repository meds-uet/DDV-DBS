module Alu_16bit(
input logic [15:0] a,
input logic [15:0] b,
input logic [2:0] Alu_control,
output logic [15:0] y
);

 always_comb begin
 case(Alu_control)
  0:  y = a+b;
  1:  y = a-b;
  2:  y = a&b;
  3:  y = a|b;
  4:  y = a^b;
 default: y=16'd0;
 endcase
 end
 
 endmodule