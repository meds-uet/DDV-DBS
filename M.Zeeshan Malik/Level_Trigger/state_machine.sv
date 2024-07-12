module state_machine (
    input logic clk,
    input logic reset,
    input logic X,
    output logic output_signal
);

    typedef enum logic [1:0] {
        IDLE  = 2'b00,
        STATE1 = 2'b01,
        STATE2 = 2'b10
    } state_t;

    state_t PS, NS; 

    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            PS <= IDLE;
        else
            PS <= NS;
    end
    
    always_comb begin
        case (PS)
            IDLE: begin
                if (X)
                    NS = IDLE;
                else
                    NS = STATE1;
            end
            STATE1: begin
                if (X)
                    NS = STATE2;
                else
                    NS = STATE1;
            end
            STATE2: begin
                if (X)
                    NS = IDLE;
                else
                    NS = STATE1;
            end
            default: NS = IDLE; // Default state cast to enum type
        endcase
    end

    always_comb begin
        case (PS)
            IDLE: output_signal = 0;
            STATE2: output_signal = 1;
            STATE1: output_signal = 0;
            default: output_signal = 0; 
        endcase
    end

endmodule
