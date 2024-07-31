
module top_module_tb;

    // Signals for the top module
    logic clk, reset, CPU_request, read_req, write_req;
    logic [31:0] address, data_in, data_out;
    integer i;

    // Instantiate the top module
    top_module uut (
        .clk(clk),                  // Connect clock signal
        .reset(reset),              // Connect reset signal
        .CPU_request(CPU_request),  // Connect CPU request signal
        .address(address),          // Connect address bus
        .data_in(data_in),          // Connect data input from CPU
        .read_req(read_req),        // Connect read request from CPU
        .write_req(write_req),      // Connect write request from CPU
        .data_out(data_out)         // Connect data output to CPU
    );

    // Clock generation
    always #5 clk = ~clk; // Toggle clock every 5 time units

    // Test sequence
    initial begin
        // Initialize signals
        clk = 0;
        reset = 0;
        CPU_request = 0;
        read_req = 0;
        write_req = 0;
        address = 32'h0;
        data_in = 32'h0;

        // Reset the system
        #10 reset = 1;
        
        // Additional delay to observe the results
        #50;

        // Test case: Write to all cache blocks
        for (i = 0; i < 8; i++) begin
            #10 CPU_request = 1; write_req = 1; address = i * 4; data_in = i;
            #10 CPU_request = 0; write_req = 0;
        end

        // Test case: Read from all cache blocks
        for (i = 0; i < 8; i++) begin
            #10 CPU_request = 1; read_req = 1; address = i * 4;
            #10 CPU_request = 0; read_req = 0;
        end

        // Test case: Cache miss and dirty bit set
        // Write to all cache blocks first to make them dirty
        for (i = 0; i < 8; i++) begin
            #10 CPU_request = 1; write_req = 1; address = i * 4; data_in = i;
            #10 CPU_request = 0; write_req = 0;
        end

        // Access an address that causes a cache miss
        #10 CPU_request = 1; read_req = 1; address = 32'h100; // Address outside the range of cache
        #10 CPU_request = 0; read_req = 0;

        
        #100 $finish; // End the simulation
    end

    // Monitor output
    initial begin
        $monitor("Time: %0t, Address: %h, Data Out: %h", $time, address, data_out); // Monitor and print signals
    end

endmodule
