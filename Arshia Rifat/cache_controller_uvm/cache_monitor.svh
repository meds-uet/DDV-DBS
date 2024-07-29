`ifndef CACHE_MONITOR_SVH
`define CACHE_MONITOR_SVH
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "cache_seq_item.svh"
`include "cache_if.svh"
class cache_monitor extends uvm_monitor;
  `uvm_component_utils(cache_monitor)

  virtual cache_if vif;
  uvm_analysis_port#(cache_seq_item) item_collected_port;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    item_collected_port = new("item_collected_port", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual cache_if)::get(this, "", "vif", vif))
      `uvm_fatal("MON", "Could not get vif")
  endfunction

  task run_phase(uvm_phase phase);
    cache_seq_item item;
    forever begin
      item = cache_seq_item::type_id::create("item");
      @(posedge vif.clk);
      if (vif.cpu_read_enable || vif.cpu_write_enable) begin
        item.address = vif.cpu_address;
        item.read_enable = vif.cpu_read_enable;
        item.write_enable = vif.cpu_write_enable;
        item.write_data = vif.cpu_write_data;
        @(posedge vif.clk);
        while(!vif.cpu_ready) @(posedge vif.clk);
        item.read_data = vif.cpu_read_data;
        item.ready = vif.cpu_ready;
        item_collected_port.write(item);
      end
    end
  endtask
endclass
`endif