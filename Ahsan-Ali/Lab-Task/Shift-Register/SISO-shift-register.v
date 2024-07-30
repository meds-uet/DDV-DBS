`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/02/2024 12:17:30 PM
// Design Name: 
// Module Name: SISO
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


module SISO( 
            input serial_in,
			input clk, rst,
			output serial_out
           );
 reg [3:0] shift_reg;

 always@(posedge clk) 
  begin
    if(rst)
        shift_reg <= 4'b0000;
    else begin
	    shift_reg[0] <= serial_in;
	    shift_reg[1] <= shift_reg[0];
	    shift_reg[2] <= shift_reg[1];
	    shift_reg[3] <= shift_reg[2];
	end
  end  

 assign serial_out = shift_reg[3]; 
 
endmodule
