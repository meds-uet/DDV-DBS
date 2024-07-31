`ifndef CACHE_AGENT_SVH
`define CACHE_AGENT_SVH

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "cache_seq_item.svh"
`include "cache_driver.svh"
`include "cache_monitor.svh"

typedef uvm_sequencer#(cache_seq_item) cache_sequencer;

class cache_agent extends uvm_agent;
  `uvm_component_utils(cache_agent)

  cache_driver    driver;
  cache_sequencer sequencer;
  cache_monitor   monitor;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    driver    = cache_driver::type_id::create("driver", this);
    sequencer = cache_sequencer::type_id::create("sequencer", this);
    monitor   = cache_monitor::type_id::create("monitor", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    driver.seq_item_port.connect(sequencer.seq_item_export);
  endfunction
endclass
`endif