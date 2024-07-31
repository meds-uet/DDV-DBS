module cache_tb;

    // Parameters
    parameter DATA_WIDTH = 32;
    parameter CACHE_SIZE = 256;
    parameter OFFSET_SIZE = 4;
    parameter INDEX_SIZE = 8;
    parameter MEMORY_SIZE = 1024;
    parameter ADDRESS_WIDTH = 32;

    // Signals
    logic clk_i;
    logic rst_i;
    logic [ADDRESS_WIDTH-1:0] processor_addr;
    logic wr_request;
    logic [DATA_WIDTH-1:0] wr_data;
    logic rd_request;
    logic [DATA_WIDTH-1:0] rd_data;

    // Cache design instance
    cache #(
        .DATA_WIDTH(DATA_WIDTH),
        .CACHE_SIZE(CACHE_SIZE),
        .OFFSET_SIZE(OFFSET_SIZE),
        .INDEX_SIZE(INDEX_SIZE),
        .MEMORY_SIZE(MEMORY_SIZE),
        .ADDRESS_WIDTH(ADDRESS_WIDTH)
    ) dut (
        .clk_i(clk_i),
        .rst_i(rst_i),
        .processor_addr(processor_addr),
        .wr_request(wr_request),
        .wr_data(wr_data),
        .rd_request(rd_request),
        .rd_data(rd_data)
    );

    // Clock generation
    always #5 clk_i = ~clk_i;

    integer i;

    initial begin
    clk_i = 1;
    rst_i = 0;
    // Initialize signals
    wr_request = 0;
    rd_request = 0;
    processor_addr = 0;
    wr_data = 0;
    #10;
    rst_i = 1;

    // Test cases: Write and read from 32 different addresses
    
    for (i = 0; i < 32; i = i + 1) begin
        // Set the data pattern for each iteration
        case (i)
            0: wr_data = 32'hAAAA_AAAA;
            1: wr_data = 32'hBBBB_BBBB;
            2: wr_data = 32'hCCCC_CCCC;
            3: wr_data = 32'hDDDD_DDDD;
            4: wr_data = 32'hEEEE_EEEE;
            5: wr_data = 32'hFFFF_FFFF;
            6: wr_data = 32'h1111_1111;
            7: wr_data = 32'h2222_2222;
            8: wr_data = 32'h3333_3333;
            9: wr_data = 32'h4444_4444;
            10: wr_data = 32'h5555_5555;
            11: wr_data = 32'h6666_6666;
            12: wr_data = 32'h7777_7777;
            13: wr_data = 32'h8888_8888;
            14: wr_data = 32'h9999_9999;
            15: wr_data = 32'h0000_AAAA;
            16: wr_data = 32'h0000_BBBB;
            17: wr_data = 32'h0000_CCCC;
            18: wr_data = 32'h0000_DDDD;
            19: wr_data = 32'h0000_EEEE;
            20: wr_data = 32'h0000_FFFF;
            21: wr_data = 32'h0000_1111;
            22: wr_data = 32'h0000_2222;
            23: wr_data = 32'h0000_3333;
            24: wr_data = 32'h0000_4444;
            25: wr_data = 32'h0000_5555;
            26: wr_data = 32'h0000_6666;
            27: wr_data = 32'h0000_7777;
            28: wr_data = 32'h0000_8888;
            29: wr_data = 32'h0000_9999;
            30: wr_data = 32'h0000_AAAA;
            31: wr_data = 32'h0000_BBBB;
            default: wr_data = 32'h0000_0000;
        endcase

        // Write to an address in memory
        wr_request = 1;
        processor_addr = i * 16; // Address offset for word-aligned memory
        #10;
        wr_request = 0;

        // Read from the same address
        #50;
        rd_request = 1;
        processor_addr = i * 16;
        #10;
        rd_request = 0;

        // Wait for a few clock cycles
        #40;
    end

    // Finish simulation
    $finish;
    end


    // Monitor read data
    initial begin
        $monitor("Time: %0t | Processor Addr: %h | Write Data: %h | Read Data: %h | rd_request: %b | wr_request: %b", 
                  $time, processor_addr, wr_data, rd_data, rd_request, wr_request);
    end

    initial begin
        $dumpfile("cache.vcd");
        $dumpvars(0,cache_tb);
    end

endmodule