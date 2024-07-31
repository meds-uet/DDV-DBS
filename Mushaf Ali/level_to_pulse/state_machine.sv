`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/09/2024 09:47:37 AM
// Design Name: 
// Module Name: level_pulse
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////
`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/08/2024 11:30:24 PM
// Design Name: 
// Module Name: fsm_s
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////
module level_to_pulse(
input logic clk,
input logic reset,
input logic x,
output logic [1:0]out_pulse //output
);
typedef enum logic [1:0] {
s0=2'b00,
s1=2'b01,
s2=2'b10
} state_t;
state_t current_state,next_state;
reg x_pre;
always_ff@(posedge clk)begin
if(reset)begin
x_pre <=0;
end
else begin
x_pre <=x;
end



end

//state_t current_state,next_state;
always_comb begin
case (current_state)
s0: if(x == x_pre) next_state=s0;else next_state=s1;
s1: if(x==x_pre) next_state=s2;else next_state=s1;
s2: if(x==x_pre) next_state=s0;else next_state=s1;
default: next_state=s0;
endcase
end
always_ff@(posedge clk)begin
if(reset)begin
current_state<=s0;
end
else begin
current_state<=next_state;
end
end
always_comb begin
case(current_state)
s0 : out_pulse=0;
s1 : out_pulse=0;
s2 : out_pulse=1;
default : out_pulse=0;
endcase
end
//assign out_state =current_state;
endmodule
