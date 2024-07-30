module tb_FIFO_Queue#(parameter DATA_WIDTH = 8,
                      parameter DEPTH = 16);

    // Signals
    logic clk;
    logic reset;
    logic read_en;
    logic write_en;
    logic [DATA_WIDTH-1:0] data_in;
    logic [DATA_WIDTH-1:0] data_out;
    logic full;
    logic empty;

    // Instantiate FIFO Queue
    FIFO_Queue#(DEPTH, DATA_WIDTH) dut (
        .clk(clk),
        .reset(reset),
        .read_en(read_en),
        .write_en(write_en),
        .data_in(data_in),
        .data_out(data_out),
        .full(full),
        .empty(empty)
    );
    

    //Clock Generation    
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end


    // Testbench Initialization
    initial begin
        reset = 1;
        read_en = 0;
        write_en = 0;
        data_in = 0;
        #10 reset = 0; // Assert reset low after 10 ns

        // Test case 1: Enqueue data and dequeue data
        // Expected behavior: data_out should match data_in in FIFO order

        // Enqueue data
        write_en = 1;
        data_in = 8'hAA; // Example data
        #20; // Wait a few cycles
        write_en = 0;

        // Dequeue data
        read_en = 1;
        #20; // Wait a few cycles
        read_en = 0;

        // Test case 2: Enqueue more data than DEPTH and check full condition

        // Enqueue more than DEPTH items
        for (int i = 0; i < DEPTH; i = i + 1) begin
            write_en = 1;
            data_in = i; // Example data
            #10; // Wait a few cycles
            write_en = 0;
        end

        // Check full condition
        write_en = 1;
        data_in = 8'hFF; // Example data
        #10; // Wait a few cycles
        write_en = 0;

        // Dequeue all items
        for (int i = 0; i < DEPTH; i = i + 1) begin
            read_en = 1;
            #10; // Wait a few cycles
            read_en = 0;
        end

        // Check empty condition
        read_en = 1;
        #10; // Wait a few cycles
        read_en = 0;

        // Finish simulation
        $finish;
    end

endmodule
