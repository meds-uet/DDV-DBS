`include "transaction.sv"

class driver;

virtual design_interface vif_driver;


mailbox gen2driver;

function new(virtual design_interface vif_driver , mailbox gen2driver);
	this.gen2driver = gen2driver;
	this.vif_driver = vif_driver;
endfunction 



task main();
	
	repeat(20) begin
		transaction tx;
		gen2driver.get(tx);

		vif_driver.in <= tx.in;

		#20;

		tx.display("DRIVER CLASS");
	end


endtask



endclass
