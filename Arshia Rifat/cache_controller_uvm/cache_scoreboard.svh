`ifndef CACHE_SCOREBOARD_SVH
`define CACHE_SCOREBOARD_SVH
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "cache_seq_item.svh"

class cache_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(cache_scoreboard)

  uvm_analysis_imp#(cache_seq_item, cache_scoreboard) item_collected_export;
  bit [31:0] mem[*];            // Associative array for memory
  bit [31:0] cache[256][16];    // Fixed-size array for cache lines
  bit valid[256];               // Fixed-size array for valid bits
  bit dirty[256];               // Fixed-size array for dirty bits

  function new(string name = "cache_scoreboard", uvm_component parent = null);
    super.new(name, parent);
    item_collected_export = new("item_collected_export", this);
  endfunction

  function void write(cache_seq_item item);
    bit [7:0] index = item.address[11:4];
    bit [3:0] offset = item.address[3:0];
    
    if (item.flush_request) begin
      flush_cache();
    end else if (item.write_enable) begin
      mem[item.address] = item.write_data;
      cache[index][offset] = item.write_data;
      valid[index] = 1;
      dirty[index] = 1;
      `uvm_info("SCB", $sformatf("Write: addr=%0h, data=%0h", item.address, item.write_data), UVM_LOW)
    end else if (item.read_enable) begin
      if (valid[index]) begin
        if (cache[index][offset] == item.read_data)
          `uvm_info("SCB", $sformatf("Read Hit: addr=%0h, data=%0h", item.address, item.read_data), UVM_LOW)
        else
          `uvm_error("SCB", $sformatf("Read Mismatch: addr=%0h, exp=%0h, got=%0h", item.address, cache[index][offset], item.read_data))
      end else begin
        if (mem.exists(item.address)) begin
          if (mem[item.address] == item.read_data)
            `uvm_info("SCB", $sformatf("Read Miss (from memory): addr=%0h, data=%0h", item.address, item.read_data), UVM_LOW)
          else
            `uvm_error("SCB", $sformatf("Read Miss Mismatch: addr=%0h, exp=%0h, got=%0h", item.address, mem[item.address], item.read_data))
        end else
          `uvm_info("SCB", $sformatf("First Read: addr=%0h, data=%0h", item.address, item.read_data), UVM_LOW)
        
        // Update cache on read miss
        cache[index] = '{default: 0};  // Clear the cache line
        cache[index][offset] = item.read_data;
        valid[index] = 1;
        dirty[index] = 0;
      end
    end
  endfunction

  function void flush_cache();
    for (int i = 0; i < 256; i++) begin
      if (valid[i] && dirty[i]) begin
        for (int j = 0; j < 16; j++) begin
          bit [31:0] addr = {i, j[3:0], 2'b00};
          mem[addr] = cache[i][j];
        end
      end
    end
    for (int i = 0; i < 256; i++) begin
      valid[i] = 0;
      dirty[i] = 0;
    end
    `uvm_info("SCB", "Cache flushed", UVM_LOW)
  endfunction
endclass
`endif
