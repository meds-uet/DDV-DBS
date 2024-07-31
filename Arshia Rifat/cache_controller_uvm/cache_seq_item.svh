`ifndef CACHE_SEQ_ITEM_SVH
`define CACHE_SEQ_ITEM_SVH
import uvm_pkg::*;
`include "uvm_macros.svh"
class cache_seq_item extends uvm_sequence_item;
  rand bit [31:0] address;
  rand bit read_enable;
  rand bit write_enable;
  rand bit [31:0] write_data;
  rand bit flush_request;
  bit [31:0] read_data;
  bit ready;

  `uvm_object_utils_begin(cache_seq_item)
    `uvm_field_int(address, UVM_ALL_ON)
    `uvm_field_int(read_enable, UVM_ALL_ON)
    `uvm_field_int(write_enable, UVM_ALL_ON)
    `uvm_field_int(write_data, UVM_ALL_ON)
    `uvm_field_int(read_data, UVM_ALL_ON)
    `uvm_field_int(ready, UVM_ALL_ON)
    `uvm_field_int(flush_request, UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name = "cache_seq_item");
    super.new(name);
  endfunction

  constraint c_read_write_mutually_exclusive {
    read_enable ^ write_enable == 1;
  }
endclass
`endif