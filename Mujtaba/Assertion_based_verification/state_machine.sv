//Level to pulse converter

module state_machine(

input clk_i,
input reset_i,
input X_i,

output logic Y_o


);



typedef enum logic [1:0]{

S0,
S1,
S2

}states;



states current_state , next_state;


//Sequential logic
always_ff @(posedge clk_i) begin
	if(reset_i) begin
		current_state <= S0;
	end

	else begin
		current_state <= next_state;
	end
end






//Combinational logic  
always_comb begin

Y_o = 1'b0;

case(current_state)

S0:
	begin
	Y_o = 1'b0;
	next_state = X_i ? S0 : S1;
	end
S1:
	begin
	Y_o = 1'b0;
	next_state = X_i ? S2 : S1;
	end
S2:
	begin
	Y_o = 1'b1;
	next_state = X_i ? S0 : S1;
	end
default:
	next_state = S0;

endcase




end





endmodule
