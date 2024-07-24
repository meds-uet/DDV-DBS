class driver;
    virtual add_if aif;
    mailbox #(transaction) mbx;
    transaction data;
  
    function new(mailbox #(transaction) mbx);
        this.mbx = mbx;
        data = new();
    endfunction 
  
    task run();
        forever begin
            mbx.get(data);
            @(posedge aif.clk);
            aif.X = data.X;
            $display("[DRV]: Interface Trigger");
            data.display();
        end
    endtask
endclass