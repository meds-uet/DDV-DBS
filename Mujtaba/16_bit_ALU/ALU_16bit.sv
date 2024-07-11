module ALU_16bit(

input [15:0]in1,
input [15:0]in2,
input [2:0]control_signal,

output logic [15:0]out

);


always_comb begin

case(control_signal)

3'b000:
    out = in1 + in2;
3'b001:
    out = in1 - in2; 
3'b010:
    out = in1 & in2;    
3'b011:
    out = in1 | in2;
3'b100:
    out = in1 ^ in2;
default:
    out = 16'hXXXX;


endcase


end



endmodule
