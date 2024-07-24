`include "generator.sv"
`include "driver.sv"
`include "input_monitor.sv"
`include "output_monitor.sv"
`include "scoreboard.sv"

class environment;
  generator gen;
  driver driv;
  input_monitor mon_in;
  output_monitor mon_out;
  scoreboard scb;
  
  mailbox gen2drv;
  mailbox mon1_scb;
  mailbox mon2_scb;
  
  virtual design_interface vif;
  
  function new(virtual design_interface vif);
    this.vif = vif;
    
    gen2drv = new();
    mon1_scb = new();
    mon2_scb = new();

    gen = new(gen2drv);
    driv = new(vif, gen2drv);
    mon_in = new(vif, mon1_scb);
    mon_out = new(vif, mon2_scb);
    scb = new(mon1_scb, mon2_scb);
  endfunction
  


  task run_test();
    fork
      gen.main();

      driv.main();
      mon_in.main();
      mon_out.main();
      scb.main();
    join_any
  endtask
  
 
endclass
