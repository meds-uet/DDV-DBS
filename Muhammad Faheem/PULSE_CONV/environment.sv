`include "generator.sv"
`include "driver.sv"
`include "monitor.sv"
`include "scoreboard.sv"

class environment;

    virtual add_if aif;
    driver drv;
    generator gen;
    monitor mon;
    scoreboard sb;
    event done;

  mailbox #(transaction) drv_mbx;
  mailbox #(transaction) mon_mbx;
  
  function new(virtual add_if aif);
   		drv_mbx = new();
        mon_mbx = new();
        drv = new(drv_mbx);
        gen = new(drv_mbx);
        mon = new(mon_mbx);
        sb = new(mon_mbx);
        drv.aif = aif;
        mon.aif = aif;
        done = gen.done;
  endfunction

  
    task run();
       fork
            gen.run();
            drv.run();
            mon.run();
            sb.run();
        join_none
        wait(done.triggered);
  endtask

endclass