module shift_reg (
    input logic clk,         
    input logic rst,         
    input logic s_in,     
    output logic [3:0] q_out   
);

    logic [3:0] shift;

    always_ff @(posedge clk) begin
        if (rst) begin
            // Synchronous reset
            shift <= 4'b0000;
        end else begin
            // Shift the data
            shift <= {shift[2:0], s_in};
        end
    end

    // Assign the internal shift register to the output
    assign q_out = shift;

endmodule
