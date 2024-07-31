module cache_controller (
    input logic clk,
    input logic reset,
    input logic CPU_request,
    input logic Cache_hit,
    input logic Cache_miss,
    input logic Dirty_bit,
    input logic Main_mem_ack,
    input logic Flush_done,
    output logic Cache_flush,
    output logic Flush,
    output logic Main_mem_access,
    output logic mem_read_req,
    output logic mem_write_req,
    output logic [2:0] state
);

    typedef enum logic [2:0] {
        IDLE = 3'b000,
        PROCESS_REQUEST = 3'b001,
        CACHE_ALLOCATE = 3'b010,
        WRITEBACK = 3'b011,
        FLUSH = 3'b100
    } state_t;

    state_t current_state, next_state;

    always_ff @(posedge clk or negedge reset) begin
        if (!reset)
            current_state <= IDLE;
        else
            current_state <= next_state;
    end

    always_comb begin
        case (current_state)
            IDLE: begin
                if (CPU_request)
                    next_state = PROCESS_REQUEST;
                else
                    next_state = IDLE;
            end
            PROCESS_REQUEST: begin
                if (Cache_hit)
                    next_state = IDLE;
                else if (Cache_miss && !Dirty_bit)
                    next_state = CACHE_ALLOCATE;
                else if (Cache_miss && Dirty_bit)
                    next_state = WRITEBACK;
                else
                    next_state = PROCESS_REQUEST;
            end
            CACHE_ALLOCATE: begin
                if (Main_mem_ack)
                    next_state = IDLE;
                else
                    next_state = CACHE_ALLOCATE;
            end
            WRITEBACK: begin
                if (Main_mem_ack && !Flush)
                    next_state = CACHE_ALLOCATE;
                else if (Main_mem_ack && Flush)
                    next_state = FLUSH;
                else
                    next_state = WRITEBACK;
            end
            FLUSH: begin
                if (Flush_done)
                    next_state = IDLE;
                else
                    next_state = FLUSH;
            end
            default: next_state = IDLE;
        endcase
    end

    always_comb begin
        Cache_flush = 1'b0;
        Flush = 1'b0;
        Main_mem_access = 1'b0;
        mem_read_req = 1'b0;
        mem_write_req = 1'b0;
        state = current_state;

        case (current_state)
            IDLE: begin
            end
            PROCESS_REQUEST: begin
                if (Cache_hit) begin
                end else if (Cache_miss) begin
                    if (Dirty_bit) begin
                        mem_write_req = 1'b1;
                    end else begin
                        mem_read_req = 1'b1;
                    end
                end
            end
            CACHE_ALLOCATE: begin
                Main_mem_access = 1'b1;
            end
            WRITEBACK: begin
                Main_mem_access = 1'b1;
                mem_write_req = 1'b1;
            end
            FLUSH: begin
                Cache_flush = 1'b1;
                Flush = 1'b1;
            end
        endcase
    end

endmodule
