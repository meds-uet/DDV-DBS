class driver;
  
  virtual fifo_if fif;     // Virtual interface to the FIFO
  mailbox #(transaction) mbx;  // Mailbox for communication
  transaction datac;       // Transaction object for communication
 
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
  endfunction; 
 
  // Reset the DUT
  task reset();
    fif.rst <= 1'b1;
    fif.rd <= 1'b0;
    fif.wr <= 1'b0;
    fif.data_in <= 0;
    repeat (5) @(posedge fif.clock);
    fif.rst <= 1'b0;
    $display("[DRV] : DUT Reset Done");
    $display("------------------------------------------");
  endtask
   
  // Write data to the FIFO
  task write();
    @(posedge fif.clock);
    fif.rst <= 1'b0;
    fif.rd <= 1'b0;
    fif.wr <= 1'b1;
    fif.data_in <= $urandom();
    @(posedge fif.clock);
    fif.wr <= 1'b0;
    $display("[DRV] : DATA WRITE  data : %0d", fif.data_in);  
    @(posedge fif.clock);
  endtask
  
  // Read data from the FIFO
  task read();  
    @(posedge fif.clock);
    fif.rst <= 1'b0;
    fif.rd <= 1'b1;
    fif.wr <= 1'b0;
    @(posedge fif.clock);
    fif.rd <= 1'b0;      
    $display("[DRV] : DATA READ");  
    @(posedge fif.clock);
  endtask
  
  // Apply random stimulus to the DUT
  task run();
    forever begin
      mbx.get(datac);  
      if (datac.oper == 1'b1)
        write();
      else
        read();
    end
  endtask
  
endclass