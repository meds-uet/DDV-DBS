module shift_reg(
    input logic clk,
    input logic reset,
    input logic serial,
    output logic serial_out
);

    logic [3:0] shift_reg;

    always_ff @(posedge clk) begin
        if (reset) begin
            shift_reg <= 0;
        end else begin
            shift_reg <= shift_reg>>1;
            shift_reg[3] <= serial;    
        end
    end

    assign serial_out = shift_reg[3];

endmodule
