`include "transaction.sv"

class driver;

//virtual interface
virtual design_interface vif_drv;

//mailbox for recieving data from generator
mailbox gen2drv;

//constructor function
function new(virtual design_interface vif_drv , mailbox gen2drv);
	this.vif_drv = vif_drv;
	this.gen2drv = gen2drv;
endfunction


///main task
task main();

$display("[DRIVER] *****************DRIVER STARTED*****************");

repeat(20) begin

	transaction tx;
	gen2drv.get(tx);
	
	@(posedge vif_drv.clk_i);
	vif_drv.in1 = tx.in1;
	vif_drv.in2 = tx.in2;
	vif_drv.en_i = tx.en_i;
	
end


$display("[DRIVER] ******************DRIVER ENDED******************");

endtask



endclass
