// word addressable memory

module cache_controller
#(
    parameter CACHE_SIZE = 16, // number of blocks
    parameter BLOCK_SIZE = 4,  // number of words in a block
    parameter MEM_SIZE = 256)  // number of blocks in main memory
(
    input  logic [$clog2(MEM_SIZE)-1:0] addr,  // input  logic [$log2(MEM_SIZE)-1:0] addr (8-bit) = 2-bit for block-size or offset in block + 4-bits for cache + 2-bit tag
    input  logic [31:0] data_in, // word addressable (4-byte data at a particular address)
    input  logic        cpu_req,
    input  logic        read_write, // 1 for write, 0 for read
    output logic [31:0] out_data,
    output  logic        main_mem_ack,
    input  logic        cache_flush,
    output logic        flush_done,
    input  logic        clk,
    input  logic        reset,
    output logic [2:0]  count,
    output logic        cache_hit_o,
    output logic [31:0] cache_data_o [CACHE_SIZE-1:0][BLOCK_SIZE-1:0],
    //output logic dirty_bit_o
    output logic        cache_dirty_o [CACHE_SIZE-1:0]
);
   
    localparam MEM_BITS = $clog2(MEM_SIZE);
    localparam BLOCK_BITS = $clog2(BLOCK_SIZE);
    localparam CACHE_BITS = $clog2(CACHE_SIZE);
    localparam TAG_BITS = MEM_BITS - CACHE_BITS - BLOCK_BITS;
   
    // Cache Parameters
    // State declaration
    typedef enum logic [2:0] {
        IDLE,
        PROCESS_REQUEST,
        CACHE_ALLOCATE,
        WRITEBACK,
        FLUSH
    } state_t;

    state_t current_state, next_state;

    // Cache structure
    logic [31:0] cache_data  [CACHE_SIZE-1:0][BLOCK_SIZE-1:0];
    logic [TAG_BITS-1:0] cache_tag   [CACHE_SIZE-1:0];
    logic        cache_valid [CACHE_SIZE-1:0];
    logic        cache_dirty [CACHE_SIZE-1:0];
    logic [31:0] main_memory [MEM_SIZE-1:0];   // word addressable (32-bits or 4-bytes at each address)

    // Cache control signals
    logic [CACHE_BITS-1:0]  index;
    logic [TAG_BITS-1:0]    tag;
    logic [BLOCK_BITS-1:0]    offset;
    logic        cache_hit;
    logic        dirty_bit;

    // Assignments
    assign cache_hit_o = cache_hit;
    assign cache_data_o = cache_data;
    assign cache_dirty_o = cache_dirty;
   

    assign offset    = addr[BLOCK_BITS-1:0];
    // Assuming 4-bit index 
    assign index  = addr[BLOCK_BITS+CACHE_BITS-1:BLOCK_BITS];
    assign tag    = addr[MEM_BITS-1:BLOCK_BITS+CACHE_BITS];

    // Output logic and cache operations
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            // Initialize memory 
            for (int i = 0; i < MEM_SIZE; i++) begin
                main_memory[i] <= i;
            end
            // Initialize cache
            for (int i = 0; i < CACHE_SIZE; i++) begin
                cache_valid[i] <= 0;
                cache_dirty[i] <= 0;
                cache_tag[i]   <= 0;
                for (int j = 0; j < BLOCK_SIZE; j++) begin
                    cache_data[i][j] <= 0;
                end
            end
            out_data <= 0;
            cache_hit <= 0;
            dirty_bit <= 0;
            count <= 0;
            flush_done <= 0;
            current_state <= IDLE;
        end else begin
            current_state <= next_state;
        end
     end
        
    always_comb begin
        case(current_state)
        IDLE: begin 
            count <= 1;
            main_mem_ack <= 0;
        
          //out_data <= 32'h0000_0000; // Default value
         //next_state <= PROCESS_REQUEST;
        end
        PROCESS_REQUEST: begin 
                       count <= 2;
                    if (cache_valid[index] && cache_tag[index] == tag) begin
                        cache_hit <= 1;
                        if (read_write) begin
                            // Write operation
                            cache_data[index][offset] <= data_in;
                            cache_dirty[index] <= 1;
                            
                            out_data <= cache_data[index][offset];
                        end else begin
                            // Read operation
                            out_data <= cache_data[index][offset];
                                                       
                        end
                    end else begin
                        cache_hit <= 0;
                        dirty_bit <= cache_dirty[index];
                    end
                    
        end
        CACHE_ALLOCATE: begin 
                    count <= 3;
                        if(!main_mem_ack)begin
                        // Load block from main memory to cache
                        for (int i = 0; i < BLOCK_SIZE; i++) begin
                            cache_data[index][i] <= main_memory[{tag, index, i}];
                        end
                        cache_valid[index] <= 1;
                        cache_dirty[index] <= 0;
                        cache_tag[index]   <= tag;
                        main_mem_ack <= 1;
                       end
           
                
        end
        WRITEBACK: begin 
                     count <= 4;
                    
                        // Write block back to main memory
                        for (int i = 0; i < BLOCK_SIZE; i++) begin
                            main_memory[{cache_tag[index], index, i}] <= cache_data[index][i];
                        end
                        cache_dirty[index] <= 0;
                        main_mem_ack <= 1;
        end
        FLUSH: begin 
                      count <= 5;
                    if (cache_flush) begin
                        // Flush all dirty blocks to main memory
                        for (int i = 0; i < CACHE_SIZE; i++) begin
                            if (cache_dirty[i]) begin
                                for (int j = 0; j < BLOCK_SIZE; j++) begin
                                    main_memory[{cache_tag[i], i, j}] <= cache_data[i][j];
                                end
                                cache_dirty[i] <= 0;
                            end
                        end
                    end
                    flush_done <= 1;

        end
        endcase
    end
    
    // Next state logic
    always_comb begin
        case (current_state)
            IDLE: begin
                if (cpu_req) begin
                    next_state = PROCESS_REQUEST;
                end else if (cache_flush) begin
                    next_state = FLUSH;
                end
            end

            PROCESS_REQUEST: begin
                if (cache_hit) begin
                    next_state = IDLE;
                end else if (!cache_hit && !dirty_bit) begin
                    next_state = CACHE_ALLOCATE;
                end else if (!cache_hit && dirty_bit) begin
                    next_state = WRITEBACK;
                end 
            end

            CACHE_ALLOCATE: begin
                if (main_mem_ack) begin
                    next_state = PROCESS_REQUEST;
                end
            end

            WRITEBACK: begin
                if (!main_mem_ack) begin
                    next_state = WRITEBACK;
                end else if (main_mem_ack && !cache_flush) begin
                    next_state = CACHE_ALLOCATE;
                end else if (main_mem_ack && cache_flush) begin
                    next_state = FLUSH;
                end
            end

            FLUSH: begin
                if (!flush_done) begin
                    next_state = WRITEBACK;
                end else if (flush_done) begin
                    next_state = IDLE;
                end
            end

            default: next_state = IDLE;
        endcase
    end

endmodule