module tb_cache_ctrl;
    // Testbench signals
    logic clk;
    logic rst;
    logic cpu_request;
    logic [31:0] address;
    logic [31:0] write_data;
    logic read;
    logic write;
    logic cache_flush;
    logic [7:0] read_data;
    logic cache_hit;
    logic [2:0] cnt;
    logic flush_done;

    // Instantiate the DUT (Device Under Test)
    cache_ctrl dut (
        .clk(clk),
        .rst(rst),
        .cpu_request(cpu_request),
        .address(address),
        .write_data(write_data),
        .read(read),
        .write(write),
        .cache_flush(cache_flush),
        .read_data(read_data),
        .cache_hit(cache_hit),
        .cnt(cnt),
        .flush_done(flush_done)
    );

  initial begin
    // Initialize signals
    clk = 0;
    cpu_request = 0;
    address = 0;
    write_data = 0;
    read = 0;
    write = 0;
    cache_flush = 0;
  end
  
    // Clock generation
    always #5 clk = ~clk;

    // Test scenarios
    initial begin
  
        // Reset the DUT
        reset();

        //Call individual test tasks
        test_read_hit();
        test_write_hit();
        test_read_miss();
        test_write_miss();
        test_writeback();
        test_cache_flush();

        // End of test
      	#50
        $finish;
    end

    // Test task: Read hit
    task test_read_hit();
        begin
            // Write data to cache first to ensure a hit
            write_to_cache(32'h0000_1104,32'hCAFEBABE);

            // Now read the same address to get a hit
            read_from_cache(32'h0000_1104);

            // Check for cache hit and correct read data
            if (cache_hit && read_data == 8'hBE) begin
                $display("Read Hit Test Passed");
            end else begin
              	$display("Read Hit Test Failed");
            end
        end
    endtask

    // Test task: Write hit
    task test_write_hit();
        begin
            // Write data to cache
          write_to_cache(32'h0000_2208,32'hdeadbeef);

            // Write again to ensure a hit
          write_to_cache(32'h0000_2208,32'hbeefcafe);

            // Check for cache hit
            if (cache_hit) begin
                $display("Write Hit Test Passed");
            end else begin
                $display("Write Hit Test Failed");
            end
        end
    endtask

    // Test task: Read miss
    task test_read_miss();
        begin
            // Read from an address not in cache
            read_from_cache(32'h0000_3310);

            // Check for cache miss and correct read data
            if (!cache_hit) begin
                $display("Read Miss Test Passed");
            end else begin
                $display("Read Miss Test Failed");
            end
        end
    endtask

    // Test task: Write miss
    task test_write_miss();
        begin
            // Write to an address not in cache
            write_to_cache(32'h0000_4407,32'hbeefcafe);
          
            // Check for cache miss
            if (!cache_hit) begin
                $display("Write Miss Test Passed");
            end else begin
                $display("Write Miss Test Failed");
            end
        end
    endtask

    // Test task: Cache flush
    task test_cache_flush();
        begin
           
            // Flush the cache
            flush_cache();

            // Check if flush is done
            if (flush_done) begin
                $display("Cache Flush Test Passed");
            end else begin
                $display("Cache Flush Test Failed");
            end
        end
    endtask

    // Test task: Writeback
    task test_writeback();
        begin
          // Write data to cache and mark it dirty
          write_to_cache(32'h0000_ab33,32'h12345678);
          
          // Now read the same address to get a hit
          read_from_cache(32'h0000_ab30);

          //update data on same line of cache to writeback dirty data in memory
          write_to_cache(32'h0000_cd33,32'habcd_efef);
          
          // Now read the old data from memory to unsure writeback 
          read_from_cache(32'h0000_ab30);

            // Check if writeback is done
          if (read_data == 8'h78) begin
                $display("Writeback Test Passed");
            end else begin
                $display("Writeback Test Failed");
            end
        end
    endtask
  
    
    // Testbench tasks
    task reset();
        begin
            rst = 1;
            #20;
            rst = 0;
            #20;
        end
    endtask

    task write_to_cache(input [31:0] addr, input [31:0] data);
        begin
            cpu_request = 1;
            address = addr;
            write_data = data;
            read = 0;
            write = 1;
            cache_flush = 0;
            @(posedge cache_hit);
            cpu_request = 0;
            @(posedge clk);
            write = 0;
        end
    endtask

    task read_from_cache(input [31:0] addr);
        begin
            cpu_request = 1;
            address = addr;
            read = 1;
            write = 0;
            cache_flush = 0;
            @(posedge cache_hit);
            cpu_request = 0;
            @(posedge clk);
            read = 0;
        end
    endtask

    task flush_cache();
        begin
            cpu_request = 0;
            read = 0;
            write = 0;
            cache_flush = 1;
            @(posedge flush_done);
            cache_flush = 0;
            @(posedge clk);
        end
    endtask

  initial begin
    // Generate VCD file for waveform viewing
    $dumpfile("dump.vcd");
    $dumpvars(0, tb_cache_ctrl);
  end

endmodule