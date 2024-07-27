covergroup spi_coverage @(posedge spi_if.clk);
  coverpoint spi_if.tx_data;
  coverpoint spi_if.rx_data;
  coverpoint spi_if.sclk;
  coverpoint spi_if.mosi;
  coverpoint spi_if.miso;
  coverpoint spi_if.ss_n;
endgroup
