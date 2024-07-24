class monitor;
    virtual add_if aif;
    mailbox #(transaction) mbx;
    transaction trans;
    function new(mailbox #(transaction) mbx);
        this.mbx = mbx;
        trans = new();
    endfunction
  
    task run();
        forever begin
            @(posedge aif.clk);
            trans.X = aif.X;
            trans.det = aif.det;
            mbx.put(trans.copy());
            $display("[MON] : DATA SENT TO SCOREBOARD");
            trans.display();
        #10;  
        end
    endtask
endclass