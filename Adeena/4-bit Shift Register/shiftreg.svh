module shift_register_4bit (
    input logic clock,      
    input logic reset,    
    input logic serial_in,  
    output logic [3:0] q    
);

    logic [3:0] shift_reg;

    
    always_ff @(posedge clock) begin
        if (reset) begin // synchronous active high
            shift_reg <= 4'b0000;  
        end else begin
            shift_reg <= {shift_reg[2:0], serial_in}; // Shift left and input new bit
        end
    end

    assign q = shift_reg;

endmodule
