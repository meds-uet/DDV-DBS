module MainMem (
    input logic clk,
    input logic [31:0] address,
    input logic write_enable,
    input logic [31:0] write_data,
    output logic [31:0] read_data,
    output logic mem_ack
);

    // the memory array (16KB main memory)
    logic [31:0] memory [4096];

    // Counter for simulating memory access delay
    logic [1:0] delay_counter;

    // Flag to indicate if an operation is in progress
    logic operation_in_progress;


    always_ff @(posedge clk) begin
        // Start operation if a write is enabled or if address is non-zero and no operation is in progress
        if (write_enable || (|address && !operation_in_progress)) begin
            operation_in_progress <= 1'b1; 
            if (write_enable) begin

                // write operation
                memory[address[13:2]] <= write_data;
                delay_counter <= 2'b11; // 3-cycle delay for write
            end else begin

                // read operation
                read_data <= memory[address[13:2]];
                delay_counter <= 2'b10; // 2-cycle delay for read
            end
        end

        // Handle delay for current operation
        if (operation_in_progress) begin
            if (delay_counter > 0) begin
                delay_counter <= delay_counter - 1; 
            end else begin
                operation_in_progress <= 1'b0; // operation complete
            end
        end

        // Acknowledge memory operation completion
        mem_ack <= operation_in_progress && (delay_counter == 0);
    end

endmodule
