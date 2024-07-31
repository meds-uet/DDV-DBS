`include "transaction.sv"

class generator;
  
  transaction tr;           // Transaction object to generate and send
  mailbox #(transaction) mbx;  // Mailbox for communication
  int count = 0;            // Number of transactions to generate
  int i = 0;                // Iteration counter
  
  event next;               // Event to signal when to send the next transaction
  event done;               // Event to convey completion of requested number of transactions
   
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
    tr = new();
  endfunction; 
 
  task run(); 
    repeat (count) begin
      assert (tr.randomize) else $error("Randomization failed");
      i++;
      mbx.put(tr);
      $display("[GEN] : Oper : %0d iteration : %0d", tr.oper, i);
      @(next);
    end -> done;
  endtask
  
endclass