`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/24/2024 10:42:35 AM
// Design Name: 
// Module Name: tb_dut
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
//////////////////////////////////////////////////.////////////////////////////////

`include "C:/Users/Hashir/DSD Internship/Scoreboard/Scoreboard.srcs/sources_1/new/scoreboard.sv"


module tb_dut;
  
  logic clk, reset;          
  logic data_in, data_out;  

 
  FF DUT (
    .clk(clk),       
    .reset(reset),  
    .a(data_in),     
    .b(data_out)     
  );

 
  scoreboard #(.DATA_WIDTH(1)) scoreboard;  

 
  initial begin
    clk = 0;              
    forever #5 clk = ~clk;  
  end

  
  initial begin
    
    scoreboard = new();  
    reset = 0;           
    data_in = 0;         
    @(posedge clk);     
    reset = 1;          
    
   
    data_in = 1'b1;    
    @(posedge clk);     
    scoreboard.add_expected(data_in);  
    scoreboard.compare_result(data_out);  
    
    
    data_in = ~data_in; 
    @(posedge clk);     
    scoreboard.add_expected(data_in);  
    scoreboard.compare_result(data_out); 
    

    repeat(10) begin
      data_in = $random % 2;  
      @(posedge clk);        
      scoreboard.add_expected(data_in);  
      scoreboard.compare_result(data_out);  
    end
    
   
    scoreboard.report_statistics();  
    
    $stop;  // End the simulation
  end
endmodule
