interface spi_if;
  logic       clk;
  logic       rst_n;
  logic [7:0] tx_data;
  logic [7:0] rx_data;
  logic       start_transaction;
  logic       transaction_done;
  logic       sclk;
  logic       mosi;
  logic       miso;
  logic       ss_n;
endinterface
