module sequential_adder(

input clk_i,
input reset_i,

input en_i,

input [15:0]in1,
input [15:0]in2,

output logic [15:0]sum


);



always_ff @(posedge clk_i) begin

if(reset_i) begin
	sum <= 16'd0;
end

else begin
	if(en_i) sum <= in1 + in2;
	else if(!en_i) sum <= 16'd0;
	else sum <= 16'dX;
end


end




endmodule
