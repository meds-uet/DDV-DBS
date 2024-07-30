class driver;
  
  virtual intf vif;
  
  mailbox gen2driv;
  
  function new (virtual intf vif, mailbox gen2driv);
    this.vif= vif;
    this.gen2driv= gen2driv;
  endfunction
  
  task main();
    
    repeat(1)
      begin
        transaction trans;
        
        gen2driv.get(trans);
        
        vif.tx_data <= trans.tx_data;
        vif.start_transaction <= trans.start_transaction;
        vif.miso <= trans.miso;
        trans.rx_data = vif.rx_data;
        trans.display("Driver");
        
      end
  endtask
endclass