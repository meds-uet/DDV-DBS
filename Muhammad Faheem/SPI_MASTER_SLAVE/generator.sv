////////////////Generator Class
class generator;
  
  transaction tr;             // Transaction object
  mailbox #(transaction) mbx; // Mailbox for transactions
  event done;                 // Done event
  int count = 0;              // Transaction count
  event drvnext;              // Event to synchronize with driver
  event sconext;              // Event to synchronize with scoreboard
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;           // Initialize mailbox
    tr = new();               // Create a new transaction
  endfunction
  
  task run();
    repeat(count) begin
      assert(tr.randomize) else $error("[GEN] :Randomization Failed");
      mbx.put(tr.copy);       // Put a copy of the transaction in the mailbox
      $display("[GEN] : din : %0d", tr.din);
      @(sconext);             // Wait for the scoreboard synchronization event
    end
    -> done;                  // Signal when done
  endtask
  