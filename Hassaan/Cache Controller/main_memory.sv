
module main_memory (
    input logic clk,                      // Clock signal
    input logic reset,                    // Reset signal
    input logic mem_read_req,             // Request to read from main memory
    input logic mem_write_req,            // Request to write to main memory
    input logic [31:0] mem_data_in,       // Data to write to main memory
    output logic [31:0] mem_data_out,     // Data read from main memory
    output logic mem_ack,                 // Acknowledge from main memory
    input logic [31:0] address            // Address to read or write
);

    // Number of memory locations
    parameter MEM_SIZE = 8;               // Example size, can be adjusted
    localparam INDEX_WIDTH = $clog2(MEM_SIZE); // Width of the index bits

    logic [31:0] memory [0:MEM_SIZE-1];   // Memory array
    logic [INDEX_WIDTH-1:0] index;        // Index extracted from address
    integer i;

    // Extract index from the address
    assign index = address[INDEX_WIDTH+1:2]; // Adjusted to match memory size

    // Initialize memory
    always_ff @(posedge clk or negedge reset) begin
        if (!reset) begin
            for (i = 0; i < MEM_SIZE; i++) begin
                memory[i] <= i;             // Initialize memory with index values
            end
            mem_data_out <= 32'h0;          // Default data output
            mem_ack <= 1'b0;                // Default acknowledge signal
        end else begin
            if (mem_read_req) begin
                mem_data_out <= memory[index]; // Read data from memory
                mem_ack <= 1'b1;             // Set acknowledge signal
            end else if (mem_write_req) begin
                memory[index] <= mem_data_in; // Write data to memory
                mem_ack <= 1'b1;             // Set acknowledge signal
            end else begin
                mem_ack <= 1'b0;             // Clear acknowledge signal
            end
        end
    end

endmodule
