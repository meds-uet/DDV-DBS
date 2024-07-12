`include "transaction.sv"

class generator;

transaction tx;

mailbox gen2driver;


function new(mailbox gen2driver);
    this.gen2driver = gen2driver;
endfunction



task main();
	repeat(20)
	begin
        tx = new();
        assert(tx.randomize());
        tx.display("GENERATOR CLASS");
        gen2driver.put(tx);
    	end
endtask


endclass
