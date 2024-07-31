
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
            aif.a = data.a;
            aif.b = data.b;
            aif.cin = data.cin;
            $display("[DRV]: Interface Trigger");
            data.display();
        end
    endtask
endclass