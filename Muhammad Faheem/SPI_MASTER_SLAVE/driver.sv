 
////////////////Driver Class
class driver;
  
  virtual spi_if vif;         // Virtual interface
  transaction tr;             // Transaction object
  mailbox #(transaction) mbx; // Mailbox for transactions
  mailbox #(bit [11:0]) mbxds; // Mailbox for data output to monitor
  event drvnext;              // Event to synchronize with generator
  
  bit [11:0] din;             // Data input
 
  function new(mailbox #(bit [11:0]) mbxds, mailbox #(transaction) mbx);
    this.mbx = mbx;           // Initialize mailboxes
    this.mbxds = mbxds;
  endfunction
  
  task reset();
    vif.rst <= 1'b1;          // Set reset signal
    vif.newd <= 1'b0;         // Clear new data flag
    vif.din <= 1'b0;          // Clear data input
    repeat(10) @(posedge vif.clk);
    vif.rst <= 1'b0;          // Clear reset signal
    repeat(5) @(posedge vif.clk);
 
    $display("[DRV] : RESET DONE");
    $display("-----------------------------------------");
  endtask
  
  task run();
    forever begin
      mbx.get(tr);            // Get a transaction from the mailbox
      vif.newd <= 1'b1;       // Set new data flag
      vif.din <= tr.din;      // Set data input
      mbxds.put(tr.din);      // Put data in the mailbox for the monitor
      @(posedge vif.sclk);
      vif.newd <= 1'b0;       // Clear new data flag
      @(posedge vif.done);
      $display("[DRV] : DATA SENT TO DAC : %0d",tr.din);
      @(posedge vif.sclk);
    end
    
  endtask