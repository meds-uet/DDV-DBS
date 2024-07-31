`timescale 1ns / 1ps

module spi_master_tb;

  localparam DELAY = 5;
  localparam CLK_DIVIDER = 4;
  localparam CPOL = 0;
  localparam CPHA = 0;

  reg clk;
  reg rst_n;
  reg start_transaction;
  reg [7:0] tx_data;
  wire [7:0] rx_data;
  wire transaction_done;
  wire sclk;
  wire mosi;
  reg miso;
  wire ss_n;
  logic [2:0] bit_count_o;
  logic [1:0] state_o;
  logic [7:0] rx_shift_o;

  spi_master #(.CLK_DIVIDER(CLK_DIVIDER), .CPOL(CPOL), .CPHA(CPHA)) uut (
    .clk(clk),
    .rst_n(rst_n),
    .start_transaction(start_transaction),
    .tx_data(tx_data),
    .rx_data(rx_data),
    .transaction_done(transaction_done),
    .sclk(sclk),
    .mosi(mosi),
    .miso(miso),
    .ss_n(ss_n),
    .bit_count_o(bit_count_o),
    .state_o(state_o),
    .rx_shift_o(rx_shift_o)
  );

  initial begin
    clk = 0;
    forever #DELAY clk = ~clk; // 10ns clock period
  end

  initial begin
    @(negedge clk);
    rst_n = 0;
    tx_data = 8'b10101010;

    @(negedge clk);
    rst_n = 1;
    start_transaction = 1;
    
    @(negedge clk);
    start_transaction = 0;
    miso = 1;
    
    @(negedge sclk);
    miso = 0;
    @(negedge sclk);
    miso = 1;
    @(negedge sclk);
    miso = 0;
    @(negedge sclk);
    miso = 1;
    @(negedge sclk);
    miso = 0;
    @(negedge sclk);
    miso = 1;
    @(negedge sclk);
    miso = 0;
    wait(transaction_done);
    #100

//    // Check received data
//    if (rx_data == 8'b111111) begin
//      $display("Test Passed: Received data = %b", rx_data);
//    end else begin
//      $display("Test Failed: Received data = %b", rx_data);
//    end

//    #10;
    $stop;
  end
endmodule
