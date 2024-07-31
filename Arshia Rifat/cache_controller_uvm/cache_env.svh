`ifndef CACHE_ENV_SVH
`define CACHE_ENV_SVH
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "cache_agent.svh"
`include "cache_scoreboard.svh"
class cache_env extends uvm_env;
  `uvm_component_utils(cache_env)

  cache_agent    agent;
  cache_scoreboard scoreboard;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent      = cache_agent::type_id::create("agent", this);
    scoreboard = cache_scoreboard::type_id::create("scoreboard", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    agent.monitor.item_collected_port.connect(scoreboard.item_collected_export);
  endfunction
endclass
`endif