module tb_fifo;

    // Parameters
    parameter WIDTH = 16;    // Width of data bus
    parameter DEPTH = 8;     // Depth of FIFO

    // Signals
    logic clk;
    logic reset;
    logic [WIDTH-1:0] data_in;
    logic wr_en;
    logic rd_en;
    logic [WIDTH-1:0] data_out;
    logic full;
    logic empty;

    // Instantiate FIFO module
    FIFO #(
        .WIDTH(WIDTH),
        .DEPTH(DEPTH)
    ) dut (
        .clk(clk),
        .reset(reset),
        .data_in(data_in),
        .wr_en(wr_en),
        .rd_en(rd_en),
        .data_out(data_out),
        .full(full),
        .empty(empty)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Reset generation
    initial begin
        reset = 1;
        #10;
        reset = 0;
    end

    // Test sequence
    initial begin
        // Test 1: Basic write and read
        wr_en = 1;
        data_in = 8'hAA;
        #5;
        wr_en = 1;
        data_in = 8'hBB;
        #5;
        wr_en = 1;
        data_in = 8'hCC;
        #5;
        rd_en = 1;
        #5;
        rd_en = 1;
        #5;
        rd_en = 1;
        #5;

        /*// Test 2: Check full and empty flags
        wr_en = 1;
        data_in = 8'hDD;
        #5;
        wr_en = 1;
        data_in = 8'hEE;
        #5;
        wr_en = 1;
        data_in = 8'hFF;
        #5;
        rd_en = 1;
        #5;
        rd_en = 1;
        #5;
        rd_en = 1;
        #5;

        // Test 3: Additional operations
        wr_en = 1;
        data_in = 8'h11;
        #5;
        wr_en = 1;
        data_in = 8'h22;
        #5;
        wr_en = 1;
        data_in = 8'h33;
        #5;
        rd_en = 1;
        #5;
        rd_en = 1;
        #5;
        rd_en = 1;
        #5;

        // Test 4: Final operations
        wr_en = 1;
        data_in = 8'h44;
        #5;
        rd_en = 1; 
        #5;
        wr_en = 1;
        data_in = 8'h55;
        #5;
        rd_en = 1;
        #5;*/

        // End simulation
        $finish;
    end

endmodule
