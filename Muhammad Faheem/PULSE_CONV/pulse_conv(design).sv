module pulse_conv(
	input reset,
	input clk,
	input X,
	output reg det
	);
reg [1:0] pr_state, nx_state; 
parameter s0=2'b00;
parameter s1=2'b01;
parameter s2=2'b10 ;
parameter s3=2'b11 ;
always_ff @(posedge clk)
begin
	if(reset)
		pr_state<=s0;
	else
	pr_state<=nx_state; 
end
always@(pr_state,X)
case(pr_state)
	s0:if(X==1)
	nx_state=s0;
	else
	nx_state=s1;
	s1:if(X==0)
	nx_state=s1;
	else
	nx_state=s2;
	s2:if(X==1)
	nx_state=s0;
	else
	nx_state=s1;

	default:nx_state=s0;
endcase

always@(pr_state)
case(pr_state)
	s0: det=0;
	s1: det=0;
	s2: det=1;
	default: det=0;
endcase
endmodule