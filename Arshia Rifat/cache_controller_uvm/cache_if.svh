interface cache_if(input logic clk, rst_n);
  logic [31:0] cpu_address;
  logic cpu_read_enable;
  logic cpu_write_enable;
  logic [31:0] cpu_write_data;
  logic [31:0] cache_read_data;
  logic [31:0] mem_read_data;
  logic flush_request;
  logic mem_ack;
  logic [31:0] cache_write_data;
  logic cache_write_enable;
  logic [31:0] mem_write_data;
  logic [31:0] mem_address;
  logic mem_write_enable;
  logic [31:0] cpu_read_data;
  logic cpu_ready;
endinterface