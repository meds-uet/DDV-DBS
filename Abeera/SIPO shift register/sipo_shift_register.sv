module sipo_shift_register (
    input logic clk,      // Clock signal
    input logic reset,    // Reset signal
    input logic serial_in, // Serial input
    output logic [3:0] parallel_out // Parallel output
);

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            parallel_out <= 4'b0000;
        end else begin
            parallel_out <= {parallel_out[2:0], serial_in};
        end
    end

endmodule