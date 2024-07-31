`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/04/2024 01:10:07 PM
// Design Name: 
// Module Name: p_fifo
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


module p_fifo(reset,clk,rd,we,data,dataout
);
parameter width=8;
parameter depth=8;
input reset,clk,rd,we;

input [width-1:0] data;
output reg [width-1:0]dataout;

  reg [width-1:0] fifo [0:depth-1];
reg fifoempty;
reg fifofull;
reg [2:0] counts_wr;
reg [2:0] counts_rd;
  reg [3:0] counts;

integer i;




  always @(posedge clk) 
 begin
   fifofull=((counts==9)? 1'b1 : 1'b0) || ((counts_wr==counts_rd) && ~fifoempty);
   fifoempty=((counts==1)? 1'b1 : 1'b0  );
 end
  always @(posedge clk ) 
begin
    if (rd && ~fifoempty) 
begin

    
counts_rd <= counts_rd + 3'b001 ;

counts <= counts - 4'b0001;

dataout <=  fifo[counts_rd] ;



       
end
  if (we && ~fifofull) 
begin

  fifo[counts_wr]<= data;
	counts_wr <= counts_wr + 3'b001 ;
	counts <= counts + 4'b0001;
 



end
    else if (reset)
begin
      counts_wr <=3'b000 ;
counts_rd <=3'b000 ;
counts <=4'b0001; 
dataout<=8'b00000000;
for (i=0; i<=width-1;i=i+1)
begin 
 fifo [i] <= 8'b00000000;
end
end


  end



endmodule

