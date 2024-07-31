module level_to_pulse_converter (
    input logic clk,
    input logic reset,
    input logic X,
    output logic out
);

    typedef enum logic [1:0] {
        S0 = 2'b00, // Idle state
        S1 = 2'b01, // Pulse detect state
        S2 = 2'b10  // Pulse generation state
    } state_transition;

    state_transition CS, NS;

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            CS <= S0;
        end else begin
            CS <= NS;
        end
    end

    always_comb begin
        case (CS)
            S0: if (X) NS = S1;
                else NS = S0;
            S1: if (!X) NS = S2;
                else NS = S1;
            S2: NS = S0;
            default: NS = S0;
        endcase
    end

    always_comb begin
        case (CS)
            S2: out = 1'b1;
            default: out = 1'b0;
        endcase
    end

endmodule
