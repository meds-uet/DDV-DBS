`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/12/2024 09:42:30 AM
// Design Name: 
// Module Name: ALU
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


module ALU(

    input [15:0]in1,
    input [15:0]in2,
    input [2:0] operation,
    output reg [16:0]out
    
    );
    reg [16:0]out1;
    always@(*)
    begin
     if (operation==0)
    begin
    out1<=in1+in2;
    end
   
   else  if (operation==1)
              begin
              out1<=in1-in2;
              end
    else  if (operation==2)
                     begin
                     out1<=in1&in2;
                     end
 else  if (operation==3)
                            begin
                            out1<=in1|in2;
                            end
    else  if (operation==4)
                                   begin
                                   out1<=in1^in2;
                                   end
                                   else
                                   out1<=0;

    end
    assign out=out1;

    

endmodule
