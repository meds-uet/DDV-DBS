`timescale 1ns / 1ps

module tb_cache_controller();

    parameter CACHE_SIZE = 16;
    parameter BLOCK_SIZE = 4;
    parameter MEM_SIZE = 256;
    parameter ADDR_WIDTH = $clog2(MEM_SIZE);

    // Inputs
    logic [ADDR_WIDTH-1:0] addr;
    logic [31:0] data_in;
    logic cpu_req;
    logic read_write;
    logic cache_flush;
    logic clk;
    logic reset;
    logic main_mem_ack;

    // Outputs
    logic [31:0] out_data;
    logic flush_done;
    logic [2:0] count;
    logic cache_hit_o;
    logic [31:0] cache_data_o[CACHE_SIZE-1:0][BLOCK_SIZE-1:0];
    logic cache_dirty_o[CACHE_SIZE-1:0];

    // Instantiate the cache controller
    cache_controller #(
        .CACHE_SIZE(CACHE_SIZE),
        .BLOCK_SIZE(BLOCK_SIZE),
        .MEM_SIZE(MEM_SIZE)
    ) uut (
        .addr(addr),
        .data_in(data_in),
        .cpu_req(cpu_req),
        .read_write(read_write),
        .out_data(out_data),
        .main_mem_ack(main_mem_ack),
        .cache_flush(cache_flush),
        .flush_done(flush_done),
        .clk(clk),
        .reset(reset),
        .count(count),
        .cache_hit_o(cache_hit_o),
        .cache_data_o(cache_data_o),
        .cache_dirty_o(cache_dirty_o)
    );

    // Clock generation
    always #5 clk = ~clk;

    // Test sequence
    initial begin
        // Initialize inputs
        clk = 0;
        reset = 1;
        addr = 0;
        data_in = 0;
        cpu_req = 0;
        read_write = 0;
        cache_flush = 0;
       // main_mem_ack = 0;

        // Reset the controller
        #10 reset = 0;

        // Test 1: Write to cache
        @(posedge clk);
        addr = 8'h04; // Arbitrary address
        data_in = 32'hDEADBEEF; // Arbitrary data
        cpu_req = 1;
        read_write = 1; // Write operation
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        
       
       
        #10;// main_mem_ack = 0;

        // Test 2: Read from cache
        @(posedge clk);
        cpu_req = 1;
       // read_write = 0; // Read operation

     
        

        // Test 3: Cache miss and allocate new block
        @(posedge clk);
        addr = 8'h10; // Arbitrary address causing cache miss
        data_in = 32'hCAFEBABE; // Arbitrary data
        cpu_req = 1;
        read_write = 1; // Write operation
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        #10;

        // Test 4: Flush the cache
        @(posedge clk);
        cpu_req = 0;
        cache_flush = 1;

        // Wait for flush_done signal
        wait(flush_done);

        // Test 5: Ensure all dirty blocks are written back to main memory
        @(posedge clk);
        // Here you would add verification logic to check main memory contents

        // Finish the simulation
        $stop;
    end

endmodule
