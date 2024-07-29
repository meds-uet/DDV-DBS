`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/08/2024 11:28:37 AM
// Design Name: 
// Module Name: pulse_genrator
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


module pulse_genrator(
input logic clk,reset,x,
output logic y



    );
    parameter [1:0]s0=2'b00;
    parameter [1:0]s1=2'b01;
    parameter [1:0]s2=2'b10;
    logic [1:0]cs,ns;
      
always_ff@(posedge clk)
begin
if(reset)
begin
cs<=0;
end
else
begin
cs<=ns;
end    
end  
always_comb
begin
case(cs)
s0: if(x==0) ns=s1; else ns =s0;
s1:if(x==0) ns=s1; else ns =s2; 
s2:if(x==0) ns=s1;  else  ns =s0;
default:ns=cs;
endcase
end 
always_comb
begin
case(cs)
s0: y=0;
s1:y=0; 
s2:y=1;
default:y=0;
endcase
end 
   
  
    
    
    
    
endmodule
