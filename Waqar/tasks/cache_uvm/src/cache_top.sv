`include "uvm_macros.svh"
import uvm_pkg::*;

`include "cache_interface.sv" //including the interface file

module cache_top;

  logic clk_i;
  
  cache_interface intf(.clk_i(clk_i));

  // Instantiate the cache module (DUT)
  cache #(
    .DATA_WIDTH(32), 
    .CACHE_SIZE(256), 
    .OFFSET_SIZE(4), 
    .INDEX_SIZE(8), 
    .MEMORY_SIZE(1024), 
    .ADDRESS_WIDTH(32)
  ) dut (
    .clk_i(intf.clk_i),
    .rst_i(intf.rst_i),
    .processor_addr(intf.processor_addr),
    .wr_request(intf.wr_request),
    .wr_data(intf.wr_data),
    .rd_request(intf.rd_request),
    .rd_data(intf.rd_data)
  );

  initial begin
    //set_method
    uvm_config_db #(virtual cache_interface)::set(null,"*","intf",intf);
  end

  initial begin
    run_test("cache_test");
  end

  // Clock generation
  initial begin
    clk_i = 0;
    forever #5 clk_i = ~clk_i; // 10 time units period
  end

  // Reset generation
  initial begin
    rst = 0;
    #10 rst = 1;
  end

  initial begin
    #1000;
    $finish();
  end

  initial begin
    $dumpfiles("cache_uvm.vcd");
    $dumpvars(0,cache_top);
  end

endmodule