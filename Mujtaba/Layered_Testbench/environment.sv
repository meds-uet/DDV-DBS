`include "generator.sv"
`include "driver.sv"
`include "monitor.sv"
`include "scoreboard.sv"


class environment;

generator gen;
driver drv;
monitor mon;
scoreboard scb;


mailbox gen2drv;
mailbox mon2scb;


virtual design_interface vif;//declaring interface handle to pass on to all compoenents 

function new(virtual design_interface vif);
	this.vif = vif;
	gen2drv = new();
	mon2scb = new();
	gen = new(gen2drv);
	drv = new(vif , gen2drv);
	mon = new(vif , mon2scb);
	scb = new(mon2scb);
endfunction



task test();
	fork
	gen.main();
	drv.main();
	mon.main();
	scb.main();
	join
endtask




task run_test();
	test();
endtask



endclass
