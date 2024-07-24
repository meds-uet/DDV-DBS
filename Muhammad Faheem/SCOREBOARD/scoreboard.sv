class scoreboard;
    mailbox #(transaction) mbx;
    transaction trans;
    event next;
    function new(mailbox #(transaction) mbx);
        this.mbx = mbx;
        trans = new();
    endfunction
  
    task run();
        forever begin
            mbx.get(trans);
            if ({trans.cout, trans.s} !== (trans.a + trans.b + trans.cin)) begin
                $display("[SCOREBOARD] : MISMATCH DETECTED");
                trans.display();
            end else begin
                $display("[SCOREBOARD] : Match");
                trans.display();
            end
         // ->next;
        end
    endtask
endclass