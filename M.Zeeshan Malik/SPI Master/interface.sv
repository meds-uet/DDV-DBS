interface intf();
  
  logic a,b,sum,carry;logic clk, rst_n;
  logic start_transaction;
  logic [7:0] tx_data, rx_data;
  logic transaction_done;
  logic sclk, mosi, miso, ss_n;
  
endinterface