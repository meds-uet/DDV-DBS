module top;
import uvm_pkg::*;
`include "uvm_macros.svh"
//`include "cache_env.svh"
//`include "cache_sequences.svh"
`include "cache_controller.svh"

  reg clk;
  reg rst_n;

  cache_if intf(clk, rst_n);
  
  cache_controller dut(
    .clk(intf.clk),
    .rst_n(intf.rst_n),
    .cpu_address(intf.cpu_address),
    .cpu_read_enable(intf.cpu_read_enable),
    .cpu_write_enable(intf.cpu_write_enable),
    .cpu_write_data(intf.cpu_write_data),
    .cpu_read_data(intf.cpu_read_data),
    .cpu_ready(intf.cpu_ready),
    .cache_read_data(intf.cache_read_data),
    .mem_read_data(intf.mem_read_data),
    .flush_request(intf.flush_request),
    .cache_write_data(intf.cache_write_data),
    .cache_write_enable(intf.cache_write_enable),
    .mem_write_data(intf.mem_write_data),
    .mem_address(intf.mem_address),
    .mem_write_enable(intf.mem_write_enable),
    .mem_ack(intf.mem_ack)

  );

  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  initial begin
    rst_n = 0;
    #10 rst_n = 1;
  end

  initial begin
    uvm_config_db#(virtual cache_if)::set(null, "*", "vif", intf);
    run_test("cache_base_test");
  end
endmodule