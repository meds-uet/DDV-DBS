module cache_controller (
    input  logic        clk,
    input  logic        reset,

    // CPU interface
    input  logic        cpu_read,
    input  logic        cpu_write,
    input  logic [31:0] cpu_addr,
    input  logic [31:0] cpu_wdata,
    output logic [31:0] cpu_rdata,
    output logic        cpu_ready,

    // Cache flush request
    input  logic        flush_request
);

    // Cache parameters
    localparam CACHE_SIZE = 256;
    localparam BLOCK_SIZE = 4;
    localparam INDEX_BITS = 8;
    localparam OFFSET_BITS = 4;
    localparam TAG_BITS = 20;

    // Cache storage
    logic [TAG_BITS-1:0] tag_array [CACHE_SIZE-1:0];
    logic                valid_array [CACHE_SIZE-1:0];
    logic                dirty_array [CACHE_SIZE-1:0];
    logic [31:0]         data_array [CACHE_SIZE-1:0][BLOCK_SIZE-1:0];

    // Internal signals
    logic [INDEX_BITS-1:0] index;
    logic [OFFSET_BITS-1:0] offset;
    logic [TAG_BITS-1:0] tag;
    logic [TAG_BITS-1:0] cached_tag;
    logic                cache_hit;
    logic                cache_miss;
    logic                cache_dirty;

    // AXI Lite signals
    logic [31:0] araddr;
    logic        arvalid;
    logic        arready;
    logic [31:0] rdata;
    logic [1:0]  rresp;
    logic        rvalid;
    logic        rready;
    
    logic [31:0] awaddr;
    logic        awvalid;
    logic        awready;
    logic [31:0] wdata;
    logic [3:0]  wstrb;
    logic        wvalid;
    logic        wready;
    logic [1:0]  bresp;
    logic        bvalid;
    logic        bready;

    // Address breakdown
    assign index = cpu_addr[INDEX_BITS+OFFSET_BITS-1:OFFSET_BITS];
    assign offset = cpu_addr[OFFSET_BITS-1:0];
    assign tag = cpu_addr[31:32-TAG_BITS];

    // Cache hit and miss detection
    assign cached_tag = tag_array[index];
    assign cache_hit = valid_array[index] && (cached_tag == tag);
    assign cache_miss = !cache_hit;
    assign cache_dirty = dirty_array[index];

    // FSM states
    typedef enum logic [2:0] {
        IDLE,
        PROCESS_REQUEST,
        CACHE_ALLOCATE,
        WRITEBACK,
        FLUSH
    } state_t;
    state_t state, next_state;

    // State transition logic
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= IDLE;
        end else begin
            state <= next_state;
        end
    end

    // Next state logic
    always_comb begin
        case (state)
            IDLE: begin
                if (cpu_read || cpu_write) begin
                    next_state = PROCESS_REQUEST;
                end else if (flush_request) begin
                    next_state = FLUSH;
                end else begin
                    next_state = IDLE;
                end
            end
            PROCESS_REQUEST: begin
                if (cache_miss) begin
                    if (cache_dirty) begin
                        next_state = WRITEBACK;
                    end else begin
                        next_state = CACHE_ALLOCATE;
                    end
                end else begin
                    next_state = IDLE;
                end
            end
            CACHE_ALLOCATE: begin
                if (arready && rvalid) begin
                    next_state = PROCESS_REQUEST;
                end else begin
                    next_state = CACHE_ALLOCATE;
                end
            end
            WRITEBACK: begin
                if (awready && bvalid) begin
                    next_state = CACHE_ALLOCATE;
                end else begin
                    next_state = WRITEBACK;
                end
            end
            FLUSH: begin
                if (awready && bvalid) begin
                    next_state = IDLE;
                end else begin
                    next_state = FLUSH;
                end
            end
            default: next_state = IDLE;
        endcase
    end

    // Output logic
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            cpu_rdata <= 32'b0;
            cpu_ready <= 0;
            arvalid <= 0;
            awvalid <= 0;
            wvalid <= 0;
            rready <= 0;
            bready <= 0;
        end else begin
            case (state)
                IDLE: begin
                    cpu_ready <= 0;
                    arvalid <= 0;
                    awvalid <= 0;
                    wvalid <= 0;
                    rready <= 0;
                    bready <= 0;
                end
                PROCESS_REQUEST: begin
                    if (cpu_read) begin
                        if (cache_hit) begin
                            cpu_rdata <= data_array[index][offset >> 2];
                            cpu_ready <= 1;
                        end else begin
                            arvalid <= 1;
                            araddr <= cpu_addr;
                        end
                    end else if (cpu_write) begin
                        if (cache_hit) begin
                            data_array[index][offset >> 2] <= cpu_wdata;
                            dirty_array[index] <= 1;
                            cpu_ready <= 1;
                        end else begin
                            arvalid <= 1;
                            araddr <= cpu_addr;
                        end
                    end
                end
                CACHE_ALLOCATE: begin
                    if (rvalid) begin
                        data_array[index][0] <= rdata;
                        data_array[index][1] <= rdata;
                        data_array[index][2] <= rdata;
                        data_array[index][3] <= rdata;
                        tag_array[index] <= tag;
                        valid_array[index] <= 1;
                        dirty_array[index] <= 0;
                        cpu_ready <= 1;
                        arvalid <= 0;
                        rready <= 1;
                    end
                end
                WRITEBACK: begin
                    if (awready) begin
                        awvalid <= 1;
                        awaddr <= {cached_tag, index, 4'b0};
                        wvalid <= 1;
                        wdata <= data_array[index][0]; // Example, you need to iterate over block size
                        wstrb <= 4'b1111; // Assuming full word write
                        dirty_array[index] <= 0;
                    end
                    if (bvalid) begin
                        bready <= 1;
                        awvalid <= 0;
                        wvalid <= 0;
                    end
                end
                FLUSH: begin
                    if (awready) begin
                        awvalid <= 1;
                        awaddr <= {cached_tag, index, 4'b0};
                        wvalid <= 1;
                        wdata <= data_array[index][0]; // Example, you need to iterate over block size
                        wstrb <= 4'b1111; // Assuming full word write
                        valid_array[index] <= 0;
                        dirty_array[index] <= 0;
                    end
                    if (bvalid) begin
                        bready <= 1;
                        awvalid <= 0;
                        wvalid <= 0;
                    end
                end
            endcase
        end
    end

    // Instantiate the AXI Lite Slave Memory
    axi_lite_slave_memory axi_mem (
        .aclk(clk),
        .aresetn(~reset),
        
        // Read address channel
        .araddr(araddr),
        .arvalid(arvalid),
        .arready(arready),
        
        // Read data channel
        .rdata(rdata),
        .rresp(rresp),
        .rvalid(rvalid),
        .rready(rready),
        
        // Write address channel
        .awaddr(awaddr),
        .awvalid(awvalid),
        .awready(awready),
        
        // Write data channel
        .wdata(wdata),
        .wstrb(wstrb),
        .wvalid(wvalid),
        .wready(wready),
        
        // Write response channel
        .bresp(bresp),
        .bvalid(bvalid),
        .bready(bready)
    );

endmodule
