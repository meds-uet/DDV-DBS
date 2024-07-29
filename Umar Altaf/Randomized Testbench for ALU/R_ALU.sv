`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/04/2024 02:26:13 PM
// Design Name: 
// Module Name: R_ALU
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


module R_ALU(

    input [15:0]in1,
    input [15:0]in2,
    input [2:0] operation,
    output logic [16:0]out
    
    );
    
    always@(*)
    begin
     if (operation==0)
    begin
    out=in1+in2;
    end
   
   else  if (operation==1)
              begin
              out=in1-in2;
              end
    else  if (operation==2)
                     begin
                     out=in1&in2;
                     end
 else  if (operation==3)
                            begin
                            out=in1|in2;
                            end
    else  if (operation==4)
                                   begin
                                   out=in1^in2;
                                   end
                                   else
                                   out=0;

    end
//    assign out=out1;

    
endmodule
