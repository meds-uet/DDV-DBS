`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 11:59:21 PM
// Design Name: 
// Module Name: decoder
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

//interface mybus();

//logic [3:0] in;
//logic [6:0] out;


//modport a1(input in, output out);

//endinterface



module decoder(
            input [3:0]in,
            output logic [6:0]out);

always_comb begin

case(in)

'b0000 : out = 'b1100111; 
'b0001 : out = 'b1111111;
'b0010 : out <= 'b1001110;
'b0011 : out <= 'b1111110;
'b0100 : out <= 'b1001111;
'b0101 : out <= 'b1000111;
'b0110 : out <= 'b1011111;

default : out = 'b1111110;

endcase

end


endmodule




