
`include "transaction.sv"

class generator;
    transaction trans;
    mailbox #(transaction) mbx;
    event done;
  
  function new(mailbox #(transaction) mbx);
        this.mbx = mbx;
        trans = new();
    endfunction
  
    task run();
 
        for (int i = 0; i < 10; i++) begin
            assert(trans.randomize()) else $display("Randomization Failed");
            mbx.put(trans.copy());
            $display("[GEN] : DATA SENT TO DRIVER");
            trans.display();
          #30;
         end
        -> done;
    endtask
  
endclass