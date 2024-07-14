`include "transaction.sv"

class output_monitor;

virtual design_interface vif_mon2;

mailbox mon2_scb;

function new(virtual design_interface vif_mon2 , mailbox mon2_scb);
	this.vif_mon2 = vif_mon2;
	this.mon2_scb = mon2_scb;
endfunction


task main();

$display("[OUTPUT MONITOR] *****************OUTPUT MONITOR STARTED*****************");

repeat(20) begin

transaction tx = new();
@(posedge vif_mon2.clk_i);
tx.sum = vif_mon2.sum;
mon2_scb.put(tx);

end

$display("[OUTPUT MONITOR] *****************OUTPUT MONITOR ENDED*****************");

endtask









endclass
