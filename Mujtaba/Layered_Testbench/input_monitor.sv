`include "transaction.sv"

class input_monitor;

virtual design_interface vif_mon1;

mailbox mon1_scb;

function new(virtual design_interface vif_mon1 , mailbox mon1_scb);
	this.vif_mon1 = vif_mon1;
	this.mon1_scb = mon1_scb;
endfunction


task main();

$display("[INPUT MONITOR] *****************INPUT MONITOR STARTED*****************");

repeat(20) begin

transaction tx = new();
@(posedge vif_mon1.clk_i);
tx.in1 = vif_mon1.in1;
tx.in2 = vif_mon1.in2;
mon1_scb.put(tx);

end

$display("[INPUT MONITOR] *****************INPUT MONITOR ENDED*****************");

endtask





endclass
