module pulse_converter (
    input logic clk,
    input logic reset,
    input logic X,
    output logic Y
);

    // State encoding
    typedef enum logic [1:0] {
        S0 = 2'b00,
        S1 = 2'b01,
        S2 = 2'b10
    } state_t;

    state_t current_state, next_state;

    // State transition always block
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            current_state <= S0;
        end else begin
            current_state <= next_state;
        end
    end

    // Next state logic always block
    always_comb begin
        case (current_state)
            S0: if (X) next_state = S0;
                else next_state = S1;
            S1: if (X) next_state = S2;
                else next_state = S1;
            S2: if (X) next_state = S0;
                else next_state = S1;
            default: next_state = S0;
        endcase
    end

    // Output logic always block
    always_comb begin
        case (current_state)
            S0: Y = 1'b0;
            S1: Y = 1'b0;
            S2: Y = 1'b1;
            default: Y = 1'b0;
        endcase
    end

endmodule