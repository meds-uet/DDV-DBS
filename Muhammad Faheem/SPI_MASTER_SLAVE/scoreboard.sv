 
////////////////Scoreboard Class
class scoreboard;
  mailbox #(bit [11:0]) mbxds, mbxms; // Mailboxes for data from driver and monitor
  bit [11:0] ds;                       // Data from driver
  bit [11:0] ms;                       // Data from monitor
  event sconext;                       // Event to synchronize with environment
  
  function new(mailbox #(bit [11:0]) mbxds, mailbox #(bit [11:0]) mbxms);
    this.mbxds = mbxds;                // Initialize mailboxes
    this.mbxms = mbxms;
  endfunction
  
  task run();
    forever begin
      mbxds.get(ds);                   // Get data from driver
      mbxms.get(ms);                   // Get data from monitor
      $display("[SCO] : DRV : %0d MON : %0d", ds, ms);
      
      if(ds == ms)
        $display("[SCO] : DATA MATCHED");
      else
        $display("[SCO] : DATA MISMATCHED");
      
      $display("-----------------------------------------");
      ->sconext;                        // Synchronize with the environment
    end
    
  endtask
  
endclass