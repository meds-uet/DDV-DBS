// cache_controller main file

module cache_controller (
    input logic clk,
    input logic rst_n,
    input logic [31:0] cpu_address,
    input logic cpu_read_enable,
    input logic cpu_write_enable,
    input logic [31:0] cpu_write_data,
    input logic [31:0] cache_read_data,
    input logic [31:0] mem_read_data,
    input logic flush_request,
    input logic mem_ack,
    output logic [31:0] cache_write_data,
    output logic cache_write_enable,
    output logic [31:0] mem_write_data,
    output logic [31:0] mem_address,
    output logic mem_write_enable,
    output logic [31:0] cpu_read_data,
    output logic cpu_ready
);

    // State machine done
    typedef enum logic [2:0] {
        IDLE = 3'b000,
        PROCESS_REQUEST = 3'b001,
        CACHE_ALLOCATE = 3'b010,
        WRITEBACK = 3'b011,
        FLUSH = 3'b100
    } state_t;

    // Defining Cache parameters
    localparam int TAG_WIDTH = 20;
    localparam int INDEX_WIDTH = 8;
    localparam int OFFSET_WIDTH = 4;

    state_t state, next_state;
    logic [TAG_WIDTH-1:0] tag_array [256];
    logic valid_array [256];
    logic dirty_bit;  // Single dirty bit
    logic [7:0] flush_index;
    logic [TAG_WIDTH-1:0] cpu_tag;
    logic [INDEX_WIDTH-1:0] cpu_index;
    logic [OFFSET_WIDTH-1:0] cpu_offset;
    logic cache_hit;
    logic flush_done;

    assign {cpu_tag, cpu_index, cpu_offset} = cpu_address;
    assign cache_hit = valid_array[cpu_index] && (tag_array[cpu_index] == cpu_tag);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            $display("Reset: state set to IDLE");
            flush_index <= '0;
            flush_done <= 1'b0;
            dirty_bit <= 1'b0;
            foreach (valid_array[i]) valid_array[i] <= 1'b0;
        end else begin
            state <= next_state;
            $display("State transition: %s -> %s", state.name(), next_state.name());
            case (state)
                PROCESS_REQUEST: begin
                    if (cache_hit && cpu_write_enable)
                        dirty_bit <= 1'b1;
                end
                CACHE_ALLOCATE: begin
                    if (next_state == PROCESS_REQUEST) begin
                        valid_array[cpu_index] <= 1'b1;
                        dirty_bit <= cpu_write_enable;
                    end
                end
                WRITEBACK: begin
                    if (next_state == CACHE_ALLOCATE)
                        dirty_bit <= 1'b0;
                end
                FLUSH: begin
                    if (next_state == IDLE) begin
                        flush_index <= '0;
                        flush_done <= 1'b1;
                    end else begin
                        flush_index <= flush_index + 1;
                        flush_done <= &flush_index;
                    end
                end
                default: ;
            endcase
        end
    end
    //Combinational logic below, initilize to all 0s

    always_comb begin
        next_state = state;
        cache_write_enable = 1'b0;
        mem_write_enable = 1'b0;
        cpu_ready = 1'b0;
        cache_write_data = '0;
        mem_write_data = '0;
        mem_address = '0;
        cpu_read_data = '0;
        
        case (state)
            IDLE: begin
                $display("IDLE: cpu_read_enable=%b, cpu_write_enable=%b, flush_request=%b", cpu_read_enable, cpu_write_enable, flush_request);
                if (cpu_read_enable || cpu_write_enable)
                    next_state = PROCESS_REQUEST;
                else if (flush_request)
                    next_state = FLUSH;
            end

            PROCESS_REQUEST: begin
                $display("PROCESS_REQUEST: cache_hit=%b, cpu_read_enable=%b, cpu_write_enable=%b", cache_hit, cpu_read_enable, cpu_write_enable);
                if (cache_hit) begin
                    next_state = IDLE;
                    cpu_ready = 1'b1;
                    if (cpu_read_enable)
                        cpu_read_data = cache_read_data;
                    if (cpu_write_enable) begin
                        cache_write_data = cpu_write_data;
                        cache_write_enable = 1'b1;
                    end
                end else if (dirty_bit) begin
                    next_state = WRITEBACK;
                    mem_address = {tag_array[cpu_index], cpu_index, {OFFSET_WIDTH{1'b0}}};
                    mem_write_data = cache_read_data;
                    mem_write_enable = 1'b1;
                end else begin
                    next_state = CACHE_ALLOCATE;
                    mem_address = {cpu_tag, cpu_index, {OFFSET_WIDTH{1'b0}}};
                end
            end
           
            CACHE_ALLOCATE: begin
                mem_address = {cpu_tag, cpu_index, {OFFSET_WIDTH{1'b0}}};
                if (mem_ack) begin
                    next_state = PROCESS_REQUEST;
                    cache_write_data = mem_read_data;
                    cache_write_enable = 1'b1;
                    tag_array[cpu_index] = cpu_tag;
                end
            end

            WRITEBACK: begin
                mem_address = {tag_array[cpu_index], cpu_index, {OFFSET_WIDTH{1'b0}}};
                mem_write_data = cache_read_data;
                mem_write_enable = 1'b1;
                if (mem_ack) begin
                    next_state = flush_request ? FLUSH : CACHE_ALLOCATE;
                    mem_write_enable = 1'b0;
                end
            end

            FLUSH: begin
                if (flush_done) begin
                    next_state = IDLE;
                end else if (valid_array[flush_index] && dirty_bit) begin
                    next_state = WRITEBACK;
                    mem_address = {tag_array[flush_index], flush_index, {OFFSET_WIDTH{1'b0}}};
                    mem_write_data = cache_read_data;
                    mem_write_enable = 1'b1;
                end
            end
        endcase
    end

endmodule