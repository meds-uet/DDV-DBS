module pulse_generator (
    input  logic clk,          // System clock
    input  logic reset_n,      // Active-low reset
    input  logic signal_in,    // Input signal to detect edges
    output logic pulse_out     // Output pulse signal
);

    // State encoding for the state machine
    typedef enum logic [1:0] {
        IDLE    = 2'b00,       // Idle state: waiting for a rising edge on signal_in
        PULSE   = 2'b01        // Pulse state: generating the output pulse
    } state_t;
    
    state_t current_state, next_state;   // Current and next state variables
    logic previous_signal;               // Register to store the previous value of signal_in

    // State transition and previous_signal update
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            // Reset condition: set the state to IDLE and clear previous_signal
            current_state <= IDLE;
            previous_signal <= 1'b0;
        end else begin
            // On clock edge, update the state and previous_signal
            current_state <= next_state;
            previous_signal <= signal_in;
        end
    end

    // Next state logic and output generation
    always_comb begin
        pulse_out = 1'b0;        // Default output to low

        // Determine next state and pulse output based on current state and input signals
        case (current_state)
            IDLE: begin
                if (signal_in && !previous_signal) begin
                    // Rising edge detected: move to PULSE state
                    next_state = PULSE;
                end else begin
                    // No rising edge: remain in IDLE state
                    next_state = IDLE;
                end
            end

            PULSE: begin
                // In PULSE state: set pulse_out high for one clock cycle
                pulse_out = 1'b1;
                // Transition back to IDLE state
                next_state = IDLE;
            end

            default: begin
                // Default state: revert to IDLE to handle unexpected cases
                next_state = IDLE;
            end
        endcase
    end

endmodule
