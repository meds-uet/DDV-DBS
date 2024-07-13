`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 02:14:55 PM
// Design Name: 
// Module Name: disp7Seg_tb
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


module Dec7Seg_tb;

    logic [3:0] BCD;
    logic [6:0] SEG;
    integer i;
    
    Dec7Seg uut (.BCD(BCD),  .SEG(SEG));
    
    initial begin
        for( i = 0; i < 16; i = i+1) //run loop for 0 to 15.
        begin
            BCD = i; 
            #10; //wait for 10 ns
        end     
    end
    endmodule