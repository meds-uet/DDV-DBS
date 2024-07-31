
module cache_controller (
    input logic clk,                  // Clock signal
    input logic reset,                // Reset signal
    input logic CPU_request,          // CPU request signal
    input logic Cache_hit,            // Cache hit signal
    input logic Cache_miss,           // Cache miss signal
    input logic Dirty_bit,            // Dirty bit signal
    input logic Main_mem_ack,         // Main memory acknowledge signal
    input logic Flush_done,           // Flush done signal
    output logic Cache_flush,         // Cache flush signal
    output logic Flush,               // Flush signal
    output logic Main_mem_access,     // Main memory access signal
    output logic mem_read_req,        // Memory read request signal
    output logic mem_write_req,       // Memory write request signal
    output logic [2:0] state          // Current state output
);

    // Definition of state types
    typedef enum logic [2:0] {
        IDLE = 3'b000,                // Idle state
        PROCESS_REQUEST = 3'b001,     // Process request state
        CACHE_ALLOCATE = 3'b010,      // Cache allocate state
        WRITEBACK = 3'b011,           // Writeback state
        FLUSH = 3'b100                // Flush state
    } state_t;

    state_t current_state, next_state; // Current and next state variables

    // State transition logic
    always_ff @(posedge clk or negedge reset) begin
        if (!reset)
            current_state <= IDLE;    // Reset to IDLE state
        else
            current_state <= next_state; // Transition to next state
    end

    // Next state logic
    always_comb begin
        case (current_state)
            IDLE: begin
                if (CPU_request)
                    next_state = PROCESS_REQUEST; // Transition to PROCESS_REQUEST on CPU request
                else
                    next_state = IDLE;            // Remain in IDLE if no CPU request
            end
            PROCESS_REQUEST: begin
                if (Cache_hit)
                    next_state = IDLE;            // Return to IDLE on cache hit
                else if (Cache_miss && !Dirty_bit)
                    next_state = CACHE_ALLOCATE;  // Transition to CACHE_ALLOCATE on cache miss and no dirty bit
                else if (Cache_miss && Dirty_bit)
                    next_state = WRITEBACK;       // Transition to WRITEBACK on cache miss and dirty bit
                else
                    next_state = PROCESS_REQUEST; // Remain in PROCESS_REQUEST if no conditions met
            end
            CACHE_ALLOCATE: begin
                if (Main_mem_ack)
                    next_state = IDLE;            // Return to IDLE on main memory acknowledge
                else
                    next_state = CACHE_ALLOCATE;  // Remain in CACHE_ALLOCATE if no main memory acknowledge
            end
            WRITEBACK: begin
                if (Main_mem_ack && !Flush)
                    next_state = CACHE_ALLOCATE;  // Transition to CACHE_ALLOCATE on main memory acknowledge and no flush
                else if (Main_mem_ack && Flush)
                    next_state = FLUSH;           // Transition to FLUSH on main memory acknowledge and flush
                else
                    next_state = WRITEBACK;       // Remain in WRITEBACK if no conditions met
            end
            FLUSH: begin
                if (Flush_done)
                    next_state = IDLE;            // Return to IDLE on flush done
                else
                    next_state = FLUSH;           // Remain in FLUSH if flush not done
            end
            default: next_state = IDLE;           // Default to IDLE state
        endcase
    end

    // Output logic
    always_comb begin
        // Default values
        Cache_flush = 1'b0;             // Default cache flush signal
        Flush = 1'b0;                   // Default flush signal
        Main_mem_access = 1'b0;         // Default main memory access signal
        mem_read_req = 1'b0;            // Default memory read request signal
        mem_write_req = 1'b0;           // Default memory write request signal
        state = current_state;          // Set current state output

        case (current_state)
            IDLE: begin
                // Idle state, waiting for CPU request
            end
            PROCESS_REQUEST: begin
                if (Cache_hit) begin
                    // Cache hit, no main memory access required
                end else if (Cache_miss) begin
                    if (Dirty_bit) begin
                        // Cache miss and dirty bit set, write back required
                        mem_write_req = 1'b1;
                    end else begin
                        // Cache miss, no write back required
                        mem_read_req = 1'b1;
                    end
                end
            end
            CACHE_ALLOCATE: begin
                Main_mem_access = 1'b1; // Main memory access required
            end
            WRITEBACK: begin
                Main_mem_access = 1'b1; // Main memory access required
                mem_write_req = 1'b1;   // Memory write request
            end
            FLUSH: begin
                Cache_flush = 1'b1;     // Cache flush signal
                Flush = 1'b1;           // Flush signal
            end
        endcase
    end

endmodule
