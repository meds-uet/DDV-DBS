`ifndef CACHE_DRIVER_SVH
`define CACHE_DRIVER_SVH
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "cache_seq_item.svh"
`include "cache_if.svh"
class cache_driver extends uvm_driver#(cache_seq_item);
  `uvm_component_utils(cache_driver)

  virtual cache_if vif;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual cache_if)::get(this, "", "vif", vif))
      `uvm_fatal("DRV", "Could not get vif")
  endfunction

  task run_phase(uvm_phase phase);
    forever begin
      seq_item_port.get_next_item(req);
      drive_item(req);
      seq_item_port.item_done();
    end
  endtask

  task drive_item(cache_seq_item item);
    @(posedge vif.clk);
    vif.cpu_address <= item.address;
    vif.cpu_read_enable <= item.read_enable;
    vif.cpu_write_enable <= item.write_enable;
    vif.cpu_write_data <= item.write_data;
    @(posedge vif.clk);
    while(!vif.cpu_ready) @(posedge vif.clk);
    item.read_data = vif.cpu_read_data;
    item.ready = vif.cpu_ready;
  endtask
endclass
`endif