`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/12/2024 12:31:50 PM
// Design Name: 
// Module Name: tb_SPI
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


module tb_SPI;

  // Testbench signals
  logic clk;
  logic rst_n;
  logic start_transaction;
  logic [7:0] tx_data;
  logic [7:0] rx_data;
  logic transaction_done;
  logic sclk;
  logic mosi;
  logic miso;
  logic ss_n;

  // Instantiate the SPI master module
  SPI ss1 (
    .clk(clk),
    .rst_n(rst_n),
    .start_transaction(start_transaction),
    .tx_data(tx_data),
    .rx_data(rx_data),
    .transaction_done(transaction_done),
    .sclk(sclk),
    .mosi(mosi),
    .miso(miso),
    .ss_n(ss_n)
  );

  // Generate clock
  initial begin
    clk = 0;
    forever #20 clk = ~clk; // 100MHz clock (10ns period)
  end


  // Reset sequence
  initial begin
    rst_n = 1;
    #50
    rst_n = 0;
  end


  initial begin
    start_transaction = 1'b0;
    #10
    start_transaction = 1'b1;
    @(posedge clk);
    tx_data = 8'b1001_1001;
    miso=1'b1;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    tx_data = 8'b1011_1011;
    @(posedge clk);
    miso=1'b1;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    
    
  end




endmodule

