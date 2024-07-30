module alu_16bit(in1, in2, sel, out);
 input logic [15:0] in1, in2;
 input logic [2:0] sel;
 output logic [15:0] out;
 
 always_comb begin
   case(sel)
     3'b000: out = in1 + in2;  //ADD
     3'b001: out = in1 - in2;  //SUB
     3'b010: out = in1 & in2;  //AND
     3'b011: out = in1 | in2;  //OR
     3'b100: out = in1 ^ in2;  //XOR
     default:
	         out = 16'd0;
   endcase
 end
 
endmodule
