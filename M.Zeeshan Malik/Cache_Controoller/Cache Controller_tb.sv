module tb_Cache_Controller;

    // Testbench signals
    logic clk;
    logic rst;
    logic read;
    logic write;
    logic c_flush;
    logic [31:0] pr_addr;
    logic [31:0] pr_data;
    logic [31:0] data_out;
    logic mem_write_req;	  
    logic [31:0] mem_addr;         
    logic [127:0] mem_read_data;
    logic mem_read_req;
    logic [127:0] mem_write_data;
    logic Ready_signal;

    // Instantiate the DUT (Device Under Test)
    Cache_Controller dut (
        .clk(clk),
        .rst(rst),
        .read(read),
        .write(write),
        .c_flush(c_flush),
        .pr_addr(pr_addr),
        .pr_data(pr_data),
        .data_out(data_out),
        .mem_write_req(mem_write_req),
        .mem_addr(mem_addr),
        .mem_read_data(mem_read_data),
        .mem_read_req(mem_read_req),
        .mem_write_data(mem_write_data),
        .Ready_signal(Ready_signal)
    );
	
	main_memory mem (
        .clk(clk),
        .rst(rst),
        .mem_write_req(mem_write_req),
        .mem_read_req(mem_read_req),
        .mem_addr(mem_addr),
        .mem_write_data(mem_write_data),
        .mem_read_data(mem_read_data),
        .Ready_signal(Ready_signal)
    );

   // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end
  
// Task to reset the DUT
  task reset_dut();
    begin
      rst = 1;
      read = 0;
      write = 0;
      c_flush = 0;
      pr_addr = 0;
      pr_data = 0;
      #20;
      rst = 0;
    end
  endtask

  // Task to write to the cache
  task write_cache(input [31:0] addr, input [31:0] data);
    begin
      @(posedge clk);
      pr_addr = addr;
      pr_data = data;
      write = 1;
      read = 0;
      c_flush = 0;
      #120;
      write = 0;
    end
  endtask

  // Task to read from the cache
  task read_cache(input [31:0] addr);
    begin
      @(posedge clk);
      pr_addr = addr;
      read = 1;
      write = 0;
      c_flush = 0;
      #90;
      read = 0;
    end
  endtask

  // Task to verify data
  task verify_data(input [31:0] expected_data);
    begin
      @(posedge clk);
      if (data_out !== expected_data) begin
        $display("ERROR: Expected %h, got %h", expected_data, data_out);
      end else begin
        $display("PASS: Data match %h", expected_data);
      end
    end
  endtask

  // Test different scenarios
  initial begin
    $display("Starting Cache Controller Testbench");

  
    reset_dut();

   
    $display("Test: Write and Read");
    write_cache(32'h0000_1000, 32'hDEAD_BEEF);
    read_cache(32'h0000_1000);
    verify_data(32'hDEAD_BEEF);

    
    $display("Test: Overwrite and Read");
    write_cache(32'h0000_1000, 32'hCAFE_BABE);
    read_cache(32'h0000_1000);
    #40
    verify_data(32'hCAFE_BABE);

 
    $display("Test: Cache Miss and Allocation");
    read_cache(32'h0000_2000); 
    
    $display("Cache Controller Testbench Complete");
    $finish;
end
endmodule