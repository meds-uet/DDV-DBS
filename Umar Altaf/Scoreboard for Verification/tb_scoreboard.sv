`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/11/2024 01:29:56 PM
// Design Name: 
// Module Name: tb_scoreboard
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

    `include "scoreboard.sv"
    `include "ALU.sv"
    
    
    module tb_scoreboard;
      // DUT signals
      logic clk, reset;
//      logic [7:0] data_in, data_out;
logic [15:0]in1,in2;
logic [2:0]operation;
logic [16:0]out;
logic [16:0] result1;
    
      // TODO: Instantiate DUT
      ALU ALU1(in1,in2,operation,out);

    
      // TODO: Instantiate Scoreboard
      // Scoreboard #(.DATA_WIDTH(8)) scoreboard;
    scoreboard #(.DATA_WIDTH(17)) scoreboard1;
      // Clock generation
      initial begin
        clk = 0;
        forever #5 clk = ~clk;
      end
    
      // Test stimulus and scoreboard usage
      initial begin
        // Initialize
        scoreboard1 = new();
        reset = 1;
//        data_in = 8'h00;
        @(posedge clk);
        reset = 0;
        @(posedge clk);
        repeat(10)
              
        begin
    @(posedge clk);
    genrator();
     
       results();   
        $display("result1 %h time %t",result1,$time);
       scoreboard1.add_expected(result1);
      $display("result1 %h time %t",result1,$time);
        @(posedge clk) scoreboard1.compare_result(out);
         $display("out %h",out);
        end
       
        // TODO: Test case 1: Simple data pass-through
        
    
        // TODO: Test case 2: Data inversion (assuming DUT inverts data)
    
        // Add more test cases here...
    
        // Report scoreboard statistics
        scoreboard1.report_statistics();
    
        $finish;
      end
      task results();
 
      
      case (operation)
      3'b000:result1=in1+in2;
      3'b001:result1=in1-in2;
      3'b010:result1=in1&in2;
      3'b011:result1=in1|in2;
      3'b100:result1=in1^in2;
      default:result1=0;
      endcase       
      endtask
      
      task genrator();
      in1=$random;
      in2=$random;
      operation=$random;        
      
      endtask
    endmodule


