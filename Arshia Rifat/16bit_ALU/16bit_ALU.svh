module 16bit_ALU( 
    input logic [15:0]in1,
    input logic [15:0]in2,
    input logic [2:0] control,
    output logic [15:0]out,
)
always_comb begin
    case(control)
    3'b000 : out = in1+ in2;
    3'b001 : out = in1- in2;
    3'b010 : out = in1  & in2;
    3'b011 :  out = in1 | in2;
    3'b100 :  out = in1^in2;
    default: out = 16'b0;
    endcase
end
endmodule