`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 02:23:36 PM
// Design Name: 
// Module Name: ALU16
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

module ALU16( input [15:0]a, b,
            input [2:0]ALUSel,
            output logic [16:0]s
    );
    
always_comb
    begin
        		case (ALUSel)
		    		0:  s = a + b;  
		    		1:  s = a - b;
		    		2:  s = a & b;
		    		3:  s = a | b;
		   		    4:  s = a ^ b;
		    		default: s <= 0;
        		endcase
    end
endmodule
