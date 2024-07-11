module fifo_queue_tb;
    parameter WIDTH = 16;
    parameter DEPTH = 32;

    logic clk;
    logic reset;
    logic enq;
    logic deq;
    logic [WIDTH-1:0] enq_data;
    logic [WIDTH-1:0] deq_data;
    logic full;
    logic empty;

    fifo_queue #(
        .WIDTH(WIDTH),
        .DEPTH(DEPTH)
    ) uut (
        .clk(clk),
        .reset(reset),
        .enq(enq),
        .deq(deq),
        .enq_data(enq_data),
        .deq_data(deq_data),
        .full(full),
        .empty(empty)
    );

    initial begin
        clk = 0;
        forever #5 clk = ~clk; 
    end

    initial begin
        reset = 1;
        enq = 0;
        deq = 0;
        enq_data = 0;

        #20 reset = 0;
        $display("Test Case 1: Enqueue and Dequeue operations");

        enq_data = 16'hAAAA;
        enq = 1;
        #10 enq = 0;
        #10;

        enq_data = 16'hBBBB;
        enq = 1;
        #10 enq = 0;
        #10;

        deq = 1;
        #10 deq = 0;
        if (deq_data !== 16'hAAAA) $display("ERROR: Expected 16'hAAAA, got %h", deq_data);

        deq = 1;
        #10 deq = 0;
        if (deq_data !== 16'hBBBB) $display("ERROR: Expected 16'hBBBB, got %h", deq_data);

        if (!empty) $display("ERROR: FIFO should be empty");


        $display("Test Case 2: Full condition");

        reset = 1;
        #20 reset = 0;
        for (int i = 0; i < DEPTH; i++) begin
            enq_data = i;
            enq = 1;
            #10 enq = 0;
            #10;
        end

        // Check full signal
        if (!full) $display("ERROR: FIFO should be full");

        enq_data = 16'hFFFF;
        enq = 1;
        #10 enq = 0;
        #10;
        if (full) $display("Correct: FIFO is full and does not enqueue");

        $display("Test Case 3: Dequeue all data");

        for (int i = 0; i < DEPTH; i++) begin
            deq = 1;
            #10 deq = 0;
            if (deq_data !== i) $display("ERROR: Expected %d, got %d", i, deq_data);
            #10;
        end

        if (!empty) $display("ERROR: FIFO should be empty");

        $display("All test cases completed");
        $finish;
    end
endmodule
