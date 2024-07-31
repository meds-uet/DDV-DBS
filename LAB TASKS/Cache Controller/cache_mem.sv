
module cache_mem (
    input logic clk,                      // Clock signal
    input logic reset,                    // Reset signal
    input logic CPU_request,              // CPU request signal
    input logic read_req,                 // Read request from CPU
    input logic write_req,                // Write request from CPU
    input logic [31:0] address,           // Address input
    input logic [31:0] data_in,           // Data input for cache write
    output logic [31:0] data_out,         // Data output
    output logic Cache_hit,               // Cache hit signal
    output logic Cache_miss,              // Cache miss signal
    output logic Dirty_bit,               // Dirty bit signal
    input logic Main_mem_ack,             // Main memory acknowledge signal
    input logic Flush_done,               // Flush done signal
    output logic Cache_flush,             // Cache flush signal
    output logic Flush,                   // Flush signal
    output logic Main_mem_access,         // Main memory access signal
    
    //output logic [31:0] mem_data_in,    // Data to write to main memory
    input logic [31:0] mem_data_out,      // Data read from main memory
    output logic mem_read_req,            // Request to read from main memory
    output logic mem_write_req            // Request to write to main memory
);

    // Number of cache sets
    parameter NUM_SETS = 8;
    // Index width to address the sets
    localparam INDEX_WIDTH = $clog2(NUM_SETS);

    // Cache structure: 8 sets, each with a tag and data block
    typedef struct {
        logic valid;                      // Valid bit
        logic dirty;                      // Dirty bit
        logic [31-INDEX_WIDTH-2:0] tag;   // Tag bits
        logic [31:0] data;                // Data block
    } cache_line;

    cache_line cache[0:NUM_SETS-1];       // Cache array
    logic [INDEX_WIDTH-1:0] index;        // Index extracted from address
    logic [31-INDEX_WIDTH-2:0] tag_bits;  // Tag bits extracted from address
    integer i;

    // Extract index and tag from the address
    assign index = address[INDEX_WIDTH + 1:2];
    assign tag_bits = address[31:INDEX_WIDTH+2];

    // Check for a hit
    assign Cache_hit = (cache[index].valid && (cache[index].tag == tag_bits));
    assign Cache_miss = !Cache_hit;
    assign Dirty_bit = (Cache_hit) ? cache[index].dirty : 1'b0;
    assign mem_read_req = (Cache_miss && !Dirty_bit);
    assign mem_write_req = (Cache_miss && Dirty_bit);

    // Initialize cache
    always_ff @(posedge clk or negedge reset) begin
        if (!reset) begin
            for (i = 0; i < NUM_SETS; i++) begin
                cache[i].valid <= 1'b0;
                cache[i].tag <= 0;
                cache[i].data <= 32'h0;
                cache[i].dirty <= 1'b0;
            end
            //mem_read_req <= 1'b0;
            //mem_write_req <= 1'b0;
        end else begin
            // Handle cache miss
            if (Cache_miss) begin
                if (Dirty_bit) begin
                    // Write back dirty cache line to main memory
                    mem_write_req <= 1'b1;
                    data_out <= cache[index].data; // Data from cache to write to memory
                end else begin
                    // Allocate new data from main memory to cache
                    mem_read_req <= 1'b1;
                end
            end else begin
                mem_read_req <= 1'b0;
                mem_write_req <= 1'b0;
            end

            // Write data to cache
            if (write_req && !Cache_miss) begin
                cache[index].valid <= 1'b1;
                cache[index].tag <= tag_bits;
                cache[index].data <= data_in;
                cache[index].dirty <= 1'b1; // Set dirty to 1 when writing data
            end
            
            // Read data from cache
            if (read_req && Cache_hit) begin
                data_out <= cache[index].data;
            end
            
            // Load data from memory into cache
            if (mem_read_req && Main_mem_ack) begin
                cache[index].valid <= 1'b1;
                cache[index].tag <= tag_bits;
                cache[index].data <= mem_data_out; // Data from memory to cache
                cache[index].dirty <= 1'b0; // Data loaded from memory is not dirty
            end

            // Handle flush operation
            if (Flush) begin
                cache[index].valid <= 1'b0;
                cache[index].tag <= 0;
                cache[index].data <= 32'h0;
                cache[index].dirty <= 1'b0;
            end
        end
    end

endmodule
