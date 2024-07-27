module tb_spi_master;
  // Instantiate the interface
  spi_if spi_vif();

  // Instantiate the DUT
  spi_master dut (
    .clk(spi_vif.clk),
    .rst_n(spi_vif.rst_n),
    .start_transaction(spi_vif.start_transaction),
    .tx_data(spi_vif.tx_data),
    .rx_data(spi_vif.rx_data),
    .transaction_done(spi_vif.transaction_done),
    .sclk(spi_vif.sclk),
    .mosi(spi_vif.mosi),
    .miso(spi_vif.miso),
    .ss_n(spi_vif.ss_n)
  );

  // Clock generation
  initial begin
    spi_vif.clk = 0;
    forever #5 spi_vif.clk = ~spi_vif.clk;
  end

  // Reset generation
  initial begin
    spi_vif.rst_n = 0;
    #20 spi_vif.rst_n = 1;
  end

  // Instantiate the driver, monitor, and scoreboard
  spi_driver drv = new(spi_vif);
  spi_monitor mon = new(spi_vif, actual_data_mbox);
  spi_scoreboard sb = new(expected_data_mbox, actual_data_mbox);

  // Instantiate the coverage group
  spi_coverage cov = new();

  // Test scenarios
  initial begin
    fork
      drv.send_transaction(8'hA5);
      drv.send_transaction(8'h5A);
      mon.monitor();
      sb.compare();
    join
  end

  // Coverage sampling
  initial begin
    forever begin
      @(posedge spi_vif.clk);
      cov.sample();
    end
  end

endmodule
