class scoreboard;
    mailbox #(transaction) mbx;
    transaction trans;
    function new(mailbox #(transaction) mbx);
        this.mbx = mbx;
        trans = new();
    endfunction
  
    task run();
        forever begin
            mbx.get(trans);
          if (trans.det == 1) begin
                $display("[SCOREBOARD] : MISMATCH DETECTED");
                trans.display();
            end else begin
              	$display("[SCOREBOARD] : Data Match");
                trans.display();
            end
        end
    endtask
endclass