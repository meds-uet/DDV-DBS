class monitor;
 
  virtual fifo_if fif;     // Virtual interface to the FIFO
  mailbox #(transaction) mbx;  // Mailbox for communication
  transaction tr;          // Transaction object for monitoring
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;     
  endfunction;
 
  task run();
    tr = new();
    
    forever begin
      repeat (2) @(posedge fif.clock);
      tr.wr = fif.wr;
      tr.rd = fif.rd;
      tr.data_in = fif.data_in;
      tr.full = fif.full;
      tr.empty = fif.empty; 
      @(posedge fif.clock);
      tr.data_out = fif.data_out;
    
      mbx.put(tr);
      $display("[MON] : Wr:%0d rd:%0d din:%0d dout:%0d full:%0d empty:%0d", tr.wr, tr.rd, tr.data_in, tr.data_out, tr.full, tr.empty);
    end
    
  endtask
  
endclass