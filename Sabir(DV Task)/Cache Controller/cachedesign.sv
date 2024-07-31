module cache_controller (
    input logic clk,
    input logic reset,
    input logic read,
    input logic write,
    input logic flush,
    input logic [31:0] address,
    input logic [31:0] write_data,
    output logic [31:0] read_data,
    output logic hit,
    output logic miss,
    output logic ready,
    output logic mem_read,
    output logic mem_write,
    output logic [31:0] mem_address,
    output logic [31:0] mem_write_data,
    input logic [31:0] mem_read_data
);

    // Parameters
    parameter IDLE = 3'b000, CHECK_CACHE = 3'b001, CACHE_HIT = 3'b010, CACHE_MISS = 3'b011, FETCH_FROM_MEM = 3'b100, UPDATE_CACHE = 3'b101, WRITE_BACK = 3'b110, FLUSH_CACHE = 3'b111, FLUSH_NEXT = 4'b1000;
    
    // State register
    logic [3:0] state, next_state;  // Increased width to 4 bits to accommodate new state
    
    // Cache memory (simple direct-mapped cache)
    logic [31:0] cache_mem [0:255];      // Data
    logic [31:0] tag_mem [0:255];        // Tags
    logic valid_mem [0:255];             // Valid bits
    logic dirty_mem [0:255];             // Dirty bits
    
    // Cache index
    logic [7:0] cache_index;
    logic [23:0] tag;
    logic hit_flag;

    // State machine
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= IDLE;
            cache_index <= 8'b0;
        end else begin
            state <= next_state;
            if (state == FLUSH_NEXT) begin
                cache_index <= cache_index + 1;
            end else if (state == IDLE && (read || write)) begin
                cache_index <= address[9:2];
                tag <= address[31:10];
            end
        end
    end
    
    // Next state logic
    always_comb begin
        next_state = state;
        case (state)
            IDLE: begin
                if (flush) begin
                    next_state = FLUSH_CACHE;
                end else if (read || write) begin
                    next_state = CHECK_CACHE;
                end
            end
            CHECK_CACHE: begin
                if (hit_flag) begin
                    next_state = CACHE_HIT;
                end else begin
                    next_state = CACHE_MISS;
                end
            end
            CACHE_HIT: begin
                next_state = IDLE;
            end
            CACHE_MISS: begin
                if (dirty_mem[cache_index]) begin
                    next_state = WRITE_BACK;
                end else begin
                    next_state = FETCH_FROM_MEM;
                end
            end
            WRITE_BACK: begin
                next_state = FETCH_FROM_MEM;
            end
            FETCH_FROM_MEM: begin
                next_state = UPDATE_CACHE;
            end
            UPDATE_CACHE: begin
                next_state = IDLE;
            end
            FLUSH_CACHE: begin
                if (dirty_mem[cache_index]) begin
                    next_state = FLUSH_NEXT;
                end else begin
                    next_state = FLUSH_CACHE;  // Loop back to FLUSH_CACHE if dirty_bit is 0
                end
            end
            FLUSH_NEXT: begin
                if (cache_index < 8'd255) begin
                    next_state = FLUSH_CACHE;
                end else begin
                    next_state = IDLE;
                end
            end
        endcase
    end
    
    // Cache hit logic
    always_comb begin
        hit_flag = (tag_mem[cache_index] == tag) && valid_mem[cache_index];
    end
    
    // Output logic
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            read_data <= 32'b0;
            hit <= 1'b0;
            miss <= 1'b0;
            ready <= 1'b0;
            mem_read <= 1'b0;
            mem_write <= 1'b0;
            mem_address <= 32'b0;
            mem_write_data <= 32'b0;
        end else begin
            case (state)
                IDLE: begin
                    ready <= 1'b1;
                    hit <= 1'b0;
                    miss <= 1'b0;
                end
                CHECK_CACHE: begin
                    ready <= 1'b0;
                    if (hit_flag) begin
                        read_data <= cache_mem[cache_index];
                        hit <= 1'b1;
                    end else begin
                        miss <= 1'b1;
                    end
                end
                CACHE_HIT: begin
                    if (write) begin
                        cache_mem[cache_index] <= write_data;
                        dirty_mem[cache_index] <= 1'b1;
                    end
                    ready <= 1'b1;
                end
                CACHE_MISS: begin
                    ready <= 1'b0;
                end
                WRITE_BACK: begin
                    mem_write <= 1'b1;
                    mem_address <= {tag_mem[cache_index], cache_index, 2'b00};
                    mem_write_data <= cache_mem[cache_index];
                end
                FETCH_FROM_MEM: begin
                    mem_write <= 1'b0;
                    mem_read <= 1'b1;
                    mem_address <= address;
                end
                UPDATE_CACHE: begin
                    mem_read <= 1'b0;
                    cache_mem[cache_index] <= mem_read_data;
                    tag_mem[cache_index] <= tag;
                    valid_mem[cache_index] <= 1'b1;
                    dirty_mem[cache_index] <= 1'b0;
                    ready <= 1'b1;
                end
                FLUSH_CACHE: begin
                    if (dirty_mem[cache_index]) begin
                        mem_write <= 1'b1;
                        mem_address <= {tag_mem[cache_index], cache_index, 2'b00};
                        mem_write_data <= cache_mem[cache_index];
                        dirty_mem[cache_index] <= 1'b0;
                    end else begin
                        mem_write <= 1'b0;
                    end
                end
            endcase
        end
    end
endmodule