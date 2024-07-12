`include "transaction.sv"

class monitor;

  virtual design_interface vif_monitor;
  mailbox mon2scb;
  transaction tx;

  function new(virtual design_interface vif_monitor, mailbox mon2scb);
    this.vif_monitor = vif_monitor;
    this.mon2scb = mon2scb;
  endfunction 

  task main;
    repeat (20) begin
      #20;
      tx = new();
      tx.in = vif_monitor.in;
      tx.binary_code = vif_monitor.binary_code;

      mon2scb.put(tx);
      tx.display("MONITOR CLASS");
    end
  endtask

endclass

