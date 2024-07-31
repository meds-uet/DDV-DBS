`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 02:49:16 PM
// Design Name: 
// Module Name: ALU_tb
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


module ALU16_tb;
logic [15:0]a, b;
logic  [2:0]ALUSel;
logic [15:0]s;
integer i;

ALU16 alu0 (.a(a), .b(b), .ALUSel(ALUSel), .s(s));

initial
begin
      a = 0;
      b = 0;
      ALUSel = 0;
      
      for (i = 0; i < 5; i = i+1) begin
         #10 a <= $random;
             b <= $random;
         	 ALUSel = i;
         	 case(i)
         	 0:  add: assert(s == (a+b)) begin $display ( "the actual and refrence results matches for addition"); end else begin $display ( "the actual and refrence results does not matches for addition");end 
         	 1:  sub: assert(s == (a-b)) begin $display ( "the actual and refrence results matches for straction"); end else begin $display ( "the actual and refrence results does not matches for substraction");end
         	 2:  and_: assert(s == (a&b)) begin $display ( "the actual and refrence results matches for AND operation"); end else begin $display ( "the actual and refrence results does not matches for AND operation");end
         	 3:  or_:  assert(s == (a|b)) begin $display ( "the actual and refrence results matches for OR operation"); end else begin $display ( "the actual and refrence results does not matches for OR operation");end
         	 4:  xor_: assert(s == (a^b)) begin $display ( "the actual and refrence results matches for xor operation"); end else begin $display ( "the actual and refrence results does not matches for xor operation");end
         	 
         	 endcase
         	 
         	
     end
   end
endmodule

