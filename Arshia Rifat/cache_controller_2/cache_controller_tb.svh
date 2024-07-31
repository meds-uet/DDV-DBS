module cache_controller_tb;

    logic clk;
    logic rst_n;
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

    // Instantiate the cache controller
    cache_controller uut (.*);

    // Clock generation
    always #5 clk = ~clk;

    // Memory model
    logic [31:0] main_memory[0:1048575];  // 4MB main memory

    // Testbench stimulus
    initial begin
        clk = 0;
        rst_n = 0;
        cpu_address = 0;
        cpu_read_enable = 0;
        cpu_write_enable = 0;
        cpu_write_data = 0;
        cache_read_data = 0;
        mem_read_data = 0;
        flush_request = 0;
        mem_ack = 0;

        // Initialize main memory
        foreach (main_memory[i]) main_memory[i] = i;

        // Power-On Reset
        #10 rst_n = 1;
        
              test_address_mapping();
              test_basic_write();
              test_basic_read();
              test_boundary_accesses();
              test_writeback_on_miss();
               #1000000; // 1ms timeout
               $display("Simulation timeout");
               $finish;

        $finish;
    end


    // Memory response
    always @(posedge clk) begin
        if (mem_write_enable) begin
            main_memory[mem_address[21:2]] <= mem_write_data;
            #20 mem_ack <= 1;
            #10 mem_ack <= 0;
        end else if (|mem_address) begin
            #20 mem_read_data <= main_memory[mem_address[21:2]];
            mem_ack <= 1;
            #10 mem_ack <= 0;
        end
    end

    // Cache response (simplified)
    always @(posedge clk) begin
        if (cache_write_enable) begin
            cache_read_data <= cache_write_data;
        end
    end

    // Test tasks
    task test_address_mapping();
        $display("Testing Address Mapping");
        perform_access(.address(32'h00000000), .is_read(1), .is_write(0), .data(32'h0)); 
        perform_access(.address(32'h00000FF0), .is_read(1), .is_write(0), .data(32'h0)); 
        perform_access(.address(32'h00001000), .is_read(1), .is_write(0), .data(32'h0)); 
        perform_access(.address(32'hFFFFFFFC), .is_read(1), .is_write(0), .data(32'h0)); 
    endtask

    task test_basic_write();
        $display("Testing Basic Write Operation");
        perform_access(.address(32'h00000100), .is_read(0), .is_write(1), .data(32'hDEADBEEF));
        perform_access(.address(32'h00000100), .is_read(0), .is_write(1), .data(32'hCAFEBABE)); 
        perform_access(.address(32'h00001100), .is_read(0), .is_write(1), .data(32'h12345678)); 
    endtask

    task test_basic_read();
        $display("Testing Basic Read Operation");
        perform_access(.address(32'h00000100), .is_read(1), .is_write(0), .data(32'h0)); 
        perform_access(.address(32'h00002100), .is_read(1), .is_write(0), .data(32'h0)); 
        repeat(5) perform_access(.address(32'h00000100), .is_read(1), .is_write(0), .data(32'h0)); 
    endtask
   
    task test_writeback_on_miss();
    $display("Testing Writeback on Cache Miss");
    perform_access(.address(32'h00000100), .is_read(0), .is_write(1), .data(32'hDEADBEEF));
    perform_access(.address(32'h00100100), .is_read(1), .is_write(0), .data(32'h0));
    endtask

    task test_boundary_accesses();
        $display("Testing Boundary Accesses");
       perform_access(.address(32'h00000FFC), .is_read(0), .is_write(1), .data(32'hBAD0BEEF)); 
       perform_access(.address(32'h00001000), .is_read(0), .is_write(1), .data(32'h12345678)); 
    endtask

    task test_write_back_logic();
        $display("Testing Write-back Logic");
        perform_access(.address(32'h00003000), .is_read(0), .is_write(1), .data(32'hDEADBEEF)); 
        perform_access(.address(32'h00103000), .is_read(1), .is_write(0), .data(32'h0)); 
        #100; // Wait for potential write-back
        if (main_memory[32'h00003000 >> 2] == 32'hDEADBEEF)
            $display("Write-back successful");
        else
            $display("Write-back failed");
    endtask

    task perform_access(input [31:0] address, input bit is_read, input bit is_write, input [31:0] data);
         $display("Performing access: address=%h, read=%b, write=%b, data=%h", address, is_read, is_write, data);
         cpu_address = address;
         cpu_read_enable = is_read;
         cpu_write_enable = is_write;
         cpu_write_data = data;
         @(posedge clk);
         $display("Waiting for cpu_ready");
         @(posedge clk);
    endtask

    // Assertions
    property cache_hit_ready;
        @(posedge clk) ((cpu_read_enable || cpu_write_enable)|-> ##[0:3] cpu_ready);
    endproperty

   
    property write_back_on_dirty_eviction;
        @(posedge clk) (uut.state == uut.WRITEBACK) |-> ##[0:10] mem_write_enable;
    endproperty
     
    property process_to_writeback_trans;
    @(posedge clk) (uut.state == uut.PROCESS_REQUEST) ##1 (uut.state == uut.WRITEBACK);
    endproperty

    // Coverage
    covergroup cache_operations_cg @(posedge clk);
        cache_hit: coverpoint {cpu_read_enable, cpu_write_enable, uut.cache_hit} {
            bins read_hit = {3'b101};
            bins write_hit = {3'b011};
            bins read_miss = {3'b100};
            bins write_miss = {3'b010};
        }
        cache_state: coverpoint uut.state {
            bins all_states[] = {uut.IDLE, uut.PROCESS_REQUEST, uut.CACHE_ALLOCATE, uut.WRITEBACK, uut.FLUSH};
            bins idle_to_process = (uut.IDLE => uut.PROCESS_REQUEST);
            bins process_to_allocate = (uut.PROCESS_REQUEST => uut.CACHE_ALLOCATE);
            bins process_to_writeback = (uut.PROCESS_REQUEST => uut.WRITEBACK);
            bins writeback_to_allocate = (uut.WRITEBACK => uut.CACHE_ALLOCATE);
        }
    endgroup

    cache_operations_cg cov_cache_ops = new();

endmodule

