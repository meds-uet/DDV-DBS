
module top_module (
    input logic clk,             // Clock input
    input logic reset,           // Reset input
    input logic CPU_request,     // CPU request signal
    input logic [31:0] address,  // Address bus from CPU
    input logic [31:0] data_in,  // Data input from CPU
    input logic read_req,        // Read request from CPU
    input logic write_req,       // Write request from CPU
    output logic [31:0] data_out // Data output to CPU
);

    // Internal signals for cache controller and memory modules
    logic Cache_hit, Cache_miss, Dirty_bit, Main_mem_ack, Flush_done;
    logic Cache_flush, Flush, Main_mem_access, mem_read_req, mem_write_req;
    logic [31:0] mem_data_out, mem_data_in;

    // Instantiate cache controller
    cache_controller cache_ctrl (
        .clk(clk),                // Connect clock signal
        .reset(reset),            // Connect reset signal
        .CPU_request(CPU_request),// Connect CPU request signal
        .Cache_hit(Cache_hit),    // Connect cache hit signal
        .Cache_miss(Cache_miss),  // Connect cache miss signal
        .Dirty_bit(Dirty_bit),    // Connect dirty bit signal
        .Main_mem_ack(Main_mem_ack), // Connect main memory acknowledge signal
        .Flush_done(Flush_done),  // Connect flush done signal
        .Cache_flush(Cache_flush),// Connect cache flush signal
        .Flush(Flush),            // Connect flush signal
        .Main_mem_access(Main_mem_access), // Connect main memory access signal
        .mem_read_req(mem_read_req), // Connect memory read request signal
        .mem_write_req(mem_write_req), // Connect memory write request signal
        .state()                  // Connect state signal
    );

    // Instantiate cache memory
    cache_mem cache (
        .clk(clk),                // Connect clock signal
        .reset(reset),            // Connect reset signal
        .CPU_request(CPU_request),// Connect CPU request signal
        .Cache_hit(Cache_hit),    // Connect cache hit signal
        .Cache_miss(Cache_miss),  // Connect cache miss signal
        .Dirty_bit(Dirty_bit),    // Connect dirty bit signal
        .Main_mem_ack(Main_mem_ack), // Connect main memory acknowledge signal
        .Flush_done(Flush_done),  // Connect flush done signal
        .Cache_flush(Cache_flush),// Connect cache flush signal
        .Flush(Flush),            // Connect flush signal
        .Main_mem_access(Main_mem_access), // Connect main memory access signal
        .data_out(data_out),      // Connect data output signal
        //.mem_data_in(mem_data_in), // Connect memory data input signal (commented out)
        .mem_data_out(mem_data_out), // Connect memory data output signal
        .mem_read_req(mem_read_req), // Connect memory read request signal
        .mem_write_req(mem_write_req), // Connect memory write request signal
        .address(address),        // Connect address bus
        .data_in(data_in),        // Connect data input from CPU
        .read_req(read_req),      // Connect read request from CPU
        .write_req(write_req)     // Connect write request from CPU
    );

    // Instantiate main memory
    main_memory main_mem (
        .clk(clk),                // Connect clock signal
        .reset(reset),            // Connect reset signal
        .mem_read_req(mem_read_req), // Connect memory read request signal
        .mem_write_req(mem_write_req), // Connect memory write request signal
        .mem_data_in(data_out),   // Connect memory data input signal
        .mem_data_out(mem_data_out), // Connect memory data output signal
        .mem_ack(Main_mem_ack),   // Connect memory acknowledge signal
        .address(address)         // Connect address bus
    );

endmodule
