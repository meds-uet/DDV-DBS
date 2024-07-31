`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/18/2024 03:58:01 PM
// Design Name: 
// Module Name: queue
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


module queue(
  input clk, reset,
  input [7:0] data_in,
  output  logic [7:0]data_out
    );
    
    logic [7:0] que[$];
    
    always @ (posedge clk or negedge reset)
    begin
    if (!reset)
    que = {};
    else begin
    que.push_back(data_in);
    que.push_back(data_in);
    //foreach(que[i]) $display("q[%d]=%d", i, que[i]);
    //@ (posedge clk)
    data_out <= que.pop_front();
    end
    end
    
endmodule
