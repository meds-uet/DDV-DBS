`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/11/2024 02:34:52 PM
// Design Name: 
// Module Name: FIFO_tb
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


module FIFO_tb;
logic clk;
logic [15:0] writeData;
logic [15:0] readData;
logic [15:0] rdata;
logic empty;
logic readEn;
logic writeEn;
logic full;
logic rstN;
logic stop;

FIFO fifo (.rstN(rstN), .writeEn (writeEn), .readEn(readEn), .clk (clk), .readData (readData), .writeData (writeData), .empty(empty), .full(full));
always #10 clk = ~clk; 

initial begin 
clk = 0;  
rstN = 0;
writeEn = 0;
readEn = 0;
stop = 0;
#50 rstN = 1;
end
initial begin
@(posedge clk);
for (int i=0; i < 50; i =i+1) begin
// Wait until there is space in fifo
while (full) 
begin
@(posedge clk);
end
// Drive new values into FIFO
writeEn = $random;
writeData = $random;
@(posedge clk);
end
stop = 1;
end

initial begin
@(posedge clk);

while (!stop) begin
    // Wait until there is data in fifo
while (empty) begin
readEn = 0;

@(posedge clk);
end

// Sample new values from FIFO at random pace
readEn = $random;
@(posedge clk);
rdata = readData;

end


end
endmodule
