module main_memory (
    input logic clk,
    input logic [31:0] address,
    input logic write_enable,
    input logic [31:0] write_data,
    output logic [31:0] read_data,
    output logic mem_ack
);

    logic [31:0] memory [4096];  // 16KB
    logic [1:0] delay_counter;
    logic operation_in_progress;

    always_ff @(posedge clk) begin
        if (write_enable || (|address && !operation_in_progress)) begin
            operation_in_progress <= 1'b1;
            if (write_enable) begin
                memory[address[13:2]] <= write_data;
                delay_counter <= 2'b11;  // delay of 3 cycles
            end else begin
                read_data <= memory[address[13:2]];
                delay_counter <= 2'b10;  // delay of 2 cycles
            end
        end

        if (operation_in_progress) begin
            if (delay_counter > 0) begin
                delay_counter <= delay_counter - 1;
            end else begin
                operation_in_progress <= 1'b0;
            end
        end

        mem_ack <= operation_in_progress && (delay_counter == 0);
    end

endmodule