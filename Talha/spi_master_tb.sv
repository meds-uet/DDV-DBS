module spi_master_tb;

    parameter DATA_WIDTH = 8;
    reg clk;
    reg reset;
    reg [DATA_WIDTH-1:0] data_in;
    reg start;
    wire [DATA_WIDTH-1:0] data_out;
    wire sclk;
    wire mosi;
    reg miso;
    wire ss;

    // Instantiate DUT
    spi_master #(
        .DATA_WIDTH(DATA_WIDTH)
    ) uut (
        .clk(clk),
        .reset(reset),
        .data_in(data_in),
        .start(start),
        .data_out(data_out),
        .sclk(sclk),
        .mosi(mosi),
        .miso(miso),
        .ss(ss)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Initialize and run test cases
    initial begin
        // Initialize signals
        reset = 1;
        data_in = 0;
        start = 0;
        miso = 0;

        // Reset the DUT
        #10 reset = 0;
        #10 reset = 1;

        // Test case 1: Simple SPI transaction
        data_in = 8'b10101010;
        start = 1;
        #10 start = 0;
        #100;

        // Verify data_out
        if (data_out == 8'b10101010) begin
            $display("Test case 1 passed");
        end else begin
            $display("Test case 1 failed");
        end

        // Test case 2: Another SPI transaction with different data
        data_in = 8'b11001100;
        start = 1;
        #10 start = 0;
        #100;

        // Verify data_out
        if (data_out == 8'b11001100) begin
            $display("Test case 2 passed");
        end else begin
            $display("Test case 2 failed");
        end

        $finish;
    end

endmodule
