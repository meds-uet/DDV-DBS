class spi_monitor;
  virtual spi_if spi_vif;
  mailbox #(logic [7:0]) rx_data_mbox;

  function new(virtual spi_if spi_vif, mailbox #(logic [7:0]) rx_data_mbox);
    this.spi_vif = spi_vif;
    this.rx_data_mbox = rx_data_mbox;
  endfunction

  task monitor();
    forever begin
      wait (spi_vif.transaction_done == 1);
      rx_data_mbox.put(spi_vif.rx_data);
    end
  endtask
endclass
