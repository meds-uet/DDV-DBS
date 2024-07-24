class monitor;
    virtual add_if aif;
    mailbox #(transaction) mbx;
    transaction trans;
   // event next;
    function new(mailbox #(transaction) mbx);
        this.mbx = mbx;
        trans = new();
    endfunction
  
    task run();
        forever begin
            trans.a = aif.a;
            trans.b = aif.b;
            trans.cin = aif.cin;
            trans.s = aif.s;
            trans.cout = aif.cout;
            mbx.put(trans.copy());
            $display("[MON] : DATA SENT TO SCOREBOARD");
            trans.display();
        #10;  // ->next;
        end
    endtask
endclass