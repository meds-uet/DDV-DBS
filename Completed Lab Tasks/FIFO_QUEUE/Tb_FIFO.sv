`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/30/2024 12:18:23 PM
// Design Name: 
// Module Name: Tb_FIFO
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


module Tb_FIFO #(
  parameter FIFO_DEPTH = 5,
  parameter FIFO_WIDTH = 8);
  
  logic clk;
  logic reset;
  logic [FIFO_WIDTH-1:0] data_in;
  logic push;
  logic pop;
  logic [FIFO_WIDTH-1:0] data_out;
  logic empty;
  logic full;
  
  // Instantiate the FIFO queue
  FIFO DUT (
    .clk(clk),
    .reset(reset),
    .data_in(data_in),
    .push(push),
    .pop(pop),
    .data_out(data_out),
    .empty(empty),
    .full(full)
  );
  
  initial begin
  clk=0;
  forever #5 clk = ~clk;
  end
  
  initial begin
    
    clk = 0;
    reset = 0;
    data_in = 0;
    push = 0;
    pop = 0;
    
    reset = 1;
    #10;
    reset = 0;
    //ENQUEUE
    data_in = 8'hAA; push = 1; #10; push = 0; #10;
    data_in = 8'hBB; push = 1; #10; push = 0; #10;
    data_in = 8'hCC; push = 1; #10; push = 0; #10;
    data_in = 8'hDD; push = 1; #10; push = 0; #10;
    data_in = 8'hEE; push = 1; #10; push = 0; #10;
    
    //DEQUEUE
    pop = 1; #10; pop = 0; #10;
    pop = 1; #10; pop = 0; #10;
    pop = 1; #10; pop = 0; #10;
    pop = 1; #10; pop = 0; #10;
    pop = 1; #10; pop = 0; #10;
    
    // Check empty and full status
    if (empty) $display("FIFO is empty");
    if (full) $display("FIFO is full");
    
    // End simulation
    #100;
    $stop;
  end
  
endmodule
