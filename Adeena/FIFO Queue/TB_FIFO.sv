module tb_fifo_queue();

    parameter DEPTH = 16;
    parameter DATA_WIDTH = 8;

    logic clk;
    logic reset;
    logic enq;
    logic deq;
    logic [DATA_WIDTH-1:0] data_in;
    logic [DATA_WIDTH-1:0] data_out;
    logic full;
    logic empty;

    fifo_queue #(DEPTH, DATA_WIDTH) uut (
        .clk(clk),
        .reset(reset),
        .enq(enq),
        .deq(deq),
        .data_in(data_in),
        .data_out(data_out),
        .full(full),
        .empty(empty)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Test sequence
    initial begin
        // Initialize inputs
        reset = 1;
        enq = 0;
        deq = 0;
        data_in = 0;

        // Reset the FIFO
        #10;
        reset = 0;

        // Enqueue data
        $display("Starting enqueue operations");
        repeat (DEPTH) begin
            @(posedge clk);
            enq = 1;
            data_in = $random;
            #10;
            enq = 0;
        end

        // Wait and check if FIFO is full
        #10;
        if (full)
            $display("FIFO is full");

        // Dequeue data
        $display("Starting dequeue operations");
        repeat (DEPTH) begin
            @(posedge clk);
            deq = 1;
            #10;
            $display("Dequeued data: %0d", data_out);
            deq = 0;
        end

        // Wait and check if FIFO is empty
        #10;
        if (empty)
            $display("FIFO is empty");

        $stop;
    end
endmodule
