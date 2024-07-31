`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 01:21:39 PM
// Design Name: 
// Module Name: Addr_4bits_tb
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


module Addr_4bits_tb;
     reg[3:0] inp1;
     reg[3:0] inp2;
     reg Cin;
     wire[3:0] sum;
     wire Cout;
    
    Addr_4bits dut(.inp1(inp1),.inp2(inp2),.Cin(Cin),.sum(sum), .Cout(Cout));
    initial begin
    Cin = 0;
    $monitor("inp1 = %b, inp2 = %b, sum = %b", inp1,inp2,sum);
    for(int i =0; i < 16; i = i+1) begin 
        for(int j = 0; j < 16; j = j+1)begin
            inp1 = i;
            inp2 = j;
            #10;
         end
     end
         $finish; 
   end

endmodule
