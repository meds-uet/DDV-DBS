`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/19/2024 02:40:44 PM
// Design Name: 
// Module Name: SPI_master_asser_tb
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


module tb_spi_master;

  // Parameters
  parameter CLK_PERIOD = 10;
  parameter DATA_WIDTH = 8;
  
  // DUT signals
  logic clk, rst_n, start_transaction;
  logic [DATA_WIDTH-1:0] tx_data, rx_data;
  logic transaction_done, sclk, mosi, miso, ss_n;
  
  // Instantiate the DUT
  spi_master dut (
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
  
  // Clock generation
  initial begin
    clk = 0;
    forever #(CLK_PERIOD/2) clk = ~clk;
  end
  
  // Reset generation
  initial begin
    rst_n = 1;
    #(2*CLK_PERIOD);
    rst_n = 0;
    #(2*CLK_PERIOD);
    rst_n = 1;
  end

  // Transaction generation
  initial begin
    start_transaction = 0;
    tx_data = 8'h00;
    @(posedge rst_n);
    
    repeat (10) begin
      // Generate constrained random data
      tx_data = $random % 256; // 8-bit data range

      // Start transaction
      start_transaction = 1;
      @(posedge clk);
      start_transaction = 0;
      
      // Wait for transaction to complete
      wait (transaction_done);
      
      // Assertions
      assert(rx_data === tx_data) else $display("Mismatch: TX data: %h, RX data: %h", tx_data, rx_data);
      
      // Check received data
      $display("Transaction complete. TX data: %h, RX data: %h", tx_data, rx_data);
      
      // Wait for a few cycles before starting the next transaction
      #(5*CLK_PERIOD);
    end
    
  
  end
  
  // MISO signal generation (loopback for testing purposes)
  assign miso = mosi; // Simple loopback for testing

endmodule
