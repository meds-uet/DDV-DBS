`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company:  DreamBig DV Training
// Engineer: Muhammad Ibrahim Shah
// 
// Create Date: 07/11/2024 11:06:36 AM
// Design Name: Pulse FSM
// Module Name: FSM
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

module PulseFSM(
input x, clk, rst,
output logic out);

typedef enum logic [1:0] 
{
s0 = 2'b00,
s1 = 2'b01,
s2 = 2'b10
} state_t;
state_t current_state, next_state;

                       // Current state Logic is sequential i.e memory
always_ff @(posedge clk or posedge rst)
begin
if (rst)
current_state <= s0;
else
current_state <= next_state;
end
                    //next state logic is Combinational
always @(*)
begin
 ////////////// Do initilize the values here Please///////////
  out = 0;
  next_state = current_state;
  
  /////// NEXT state Transition Logic
case (current_state)
    s0: if (x) 
	        next_state = s1;
        else 
	        next_state = s0;

    s1: if (x) 
	       next_state = s2;
        else 
	       next_state = s1;

    s2: if (x) 
	       next_state = s0;
        else 
	       next_state = s1;
endcase
end

always @(*)
begin
if (next_state==s2)
out = 1;
else 
out = 0;
end
endmodule