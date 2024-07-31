// Code your testbench here
// or browse Examples
`include "interface.sv"
`include "test"

module testbench;
  intf i_intf();
  
  test t1(i_intf);
  
  spi_master uut (
    .clk(i_intf.clk),
    .rst_n(i_intf.rst_n),
    .start_transaction(i_intf.start_transaction),
    .tx_data(i_intf.tx_data),
    .rx_data(i_intf.rx_data),
    .transaction_done(i_intf.transaction_done),
    .sclk(i_intf.sclk),
    .mosi(i_intf.mosi),
    .miso(i_intf.miso),
    .ss_n(i_intf.ss_n)
  );

  // Clock generation
  initial begin
    i_intf.clk = 0;
    forever #5 i_intf.clk = ~i_intf.clk;  // 100 MHz clock
  end

  // Reset generation
  initial begin
    i_intf.rst_n = 0;
    #20;
    i_intf.rst_n = 1;
  end
  
endmodule

 
