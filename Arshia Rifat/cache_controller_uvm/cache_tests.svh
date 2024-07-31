import uvm_pkg::*;
`include "uvm_macros.svh"
`include "cache_env.svh"
`include "cache_sequences.svh"
class cache_base_test extends uvm_test;
  `uvm_component_utils(cache_base_test)

  cache_env env;

  function new(string name = "cache_base_test", uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = cache_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    cache_base_seq seq;
    phase.raise_objection(this);
    seq = cache_base_seq::type_id::create("seq");
    seq.start(env.agent.sequencer);
    phase.drop_objection(this);
  endtask
endclass

class cache_write_test extends cache_base_test;
  `uvm_component_utils(cache_write_test)

  function new(string name = "cache_write_test", uvm_component parent);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    cache_write_seq seq;
    phase.raise_objection(this);
    seq = cache_write_seq::type_id::create("seq");
    seq.start(env.agent.sequencer);
    phase.drop_objection(this);
  endtask
endclass

class cache_read_test extends cache_base_test;
  `uvm_component_utils(cache_read_test)

  function new(string name = "cache_read_test", uvm_component parent);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    cache_read_seq seq;
    phase.raise_objection(this);
    seq = cache_read_seq::type_id::create("seq");
    seq.start(env.agent.sequencer);
    phase.drop_objection(this);
  endtask
endclass

class cache_mixed_test extends cache_base_test;
  `uvm_component_utils(cache_mixed_test)

  function new(string name = "cache_mixed_test", uvm_component parent);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    cache_mixed_seq seq;
    phase.raise_objection(this);
    seq = cache_mixed_seq::type_id::create("seq");
    seq.start(env.agent.sequencer);
    phase.drop_objection(this);
  endtask
endclass

class cache_flush_test extends cache_base_test;
  `uvm_component_utils(cache_flush_test)

  function new(string name = "cache_flush_test", uvm_component parent);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    cache_write_seq write_seq;
    cache_flush_seq flush_seq;
    cache_read_seq read_seq;
    
    phase.raise_objection(this);
    
    write_seq = cache_write_seq::type_id::create("write_seq");
    write_seq.start(env.agent.sequencer);
    
    flush_seq = cache_flush_seq::type_id::create("flush_seq");
    flush_seq.start(env.agent.sequencer);
    
    read_seq = cache_read_seq::type_id::create("read_seq");
    read_seq.start(env.agent.sequencer);
    
    phase.drop_objection(this);
  endtask
endclass