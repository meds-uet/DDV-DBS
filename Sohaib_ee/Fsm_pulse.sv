// Code your design here

module Fsm_pulse(
input logic clk,
input logic rst,
input logic x,
output logic y

);
parameter S0=2'b00;
parameter S1=2'b01;
parameter S2=2'b10;

logic [1:0] PS,NS;

// Present state logic
 
  always_ff @(posedge clk ) begin
  if(rst) PS <= S0;
  else    PS <= NS;

end

// Next state logic
always_comb begin
  case(PS)
  S0: if(x) NS=S0;
      else  NS=S1;
  S1: if (x) NS=S2;
      else   NS=S1;
  S2: if (x) NS=S0;
      else   NS=S1;
	default : NS=S0;
	endcase
end	 

//Output logic 
always_comb begin

	case(PS) 
	S0: y=0;
	S1: y=0;
	S2: y=1;
default: y=1'bx;
    endcase
	end


endmodule