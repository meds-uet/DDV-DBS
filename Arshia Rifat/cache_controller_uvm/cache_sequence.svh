import uvm_pkg::*;
`include "uvm_macros.svh"
`include "cache_seq_item.svh"
class cache_base_seq extends uvm_sequence#(cache_seq_item);
  `uvm_object_utils(cache_base_seq)

  function new(string name = "cache_base_seq");
    super.new(name);
  endfunction

  task body();
    cache_seq_item req;
    repeat(10) begin
      req = cache_seq_item::type_id::create("req");
      start_item(req);
      if (!req.randomize()) `uvm_error("SEQ", "Randomization failed")
      finish_item(req);
    end
  endtask
endclass
class cache_write_seq extends cache_base_seq;
  `uvm_object_utils(cache_write_seq)

  function new(string name = "cache_write_seq");
    super.new(name);
  endfunction

  task body();
    cache_seq_item req;
    repeat(10) begin
      req = cache_seq_item::type_id::create("req");
      start_item(req);
      assert(req.randomize() with { write_enable == 1; read_enable == 0; });
      finish_item(req);
    end
  endtask
endclass

class cache_read_seq extends cache_base_seq;
  `uvm_object_utils(cache_read_seq)

  function new(string name = "cache_read_seq");
    super.new(name);
  endfunction

  task body();
    cache_seq_item req;
    repeat(10) begin
      req = cache_seq_item::type_id::create("req");
      start_item(req);
      assert(req.randomize() with { read_enable == 1; write_enable == 0; });
      finish_item(req);
    end
  endtask
endclass

class cache_mixed_seq extends cache_base_seq;
  `uvm_object_utils(cache_mixed_seq)

  function new(string name = "cache_mixed_seq");
    super.new(name);
  endfunction

  task body();
    cache_seq_item req;
    repeat(20) begin
      req = cache_seq_item::type_id::create("req");
      start_item(req);
      assert(req.randomize());
      finish_item(req);
    end
  endtask
endclass

class cache_flush_seq extends cache_base_seq;
  `uvm_object_utils(cache_flush_seq)

  function new(string name = "cache_flush_seq");
    super.new(name);
  endfunction

  task body();
    cache_seq_item req;
    req = cache_seq_item::type_id::create("req");
    start_item(req);
    req.flush_request = 1;
    finish_item(req);
  endtask
endclass