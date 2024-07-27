class spi_driver;
  virtual spi_if spi_vif;

  function new(virtual spi_if spi_vif);
    this.spi_vif = spi_vif;
  endfunction

  task send_transaction(input logic [7:0] data);
    spi_vif.tx_data <= data;
    spi_vif.start_transaction <= 1;
    wait (spi_vif.transaction_done == 1);
    spi_vif.start_transaction <= 0;
  endtask
endclass
