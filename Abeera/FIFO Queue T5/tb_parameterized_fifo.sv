module tb_parameterized_fifo;
parameter DEPTH = 16; //This also means number of elements it can  depth wise
parameter WIDTH = 8; //This means the width that is 8 max
logic en;
logic deq;
logic clk;
logic reset;
logic [WIDTH - 1:0] datain;
logic [WIDTH -1: 0] dataout;
logic full;
logic empty;
int i;

parameterized_fifo #(
    .DEPTH(DEPTH),
    .WIDTH(WIDTH)
)uut(
     .clk(clk),
        .reset(reset),
        .enq(enq),
        .deq(deq),
        .din(din),
        .dout(dout),
        .full(full),
        .empty(empty)
);

initial begin
    clk = 0;
    forever #5 clk = ~clk;
end

initial begin
    // Initialize signals
        reset = 1;
        enq = 0;
        deq = 0;
        din = 0;

        // Reset the FIFO
        #10 reset = 0;
        #10 reset = 1;

        // Test 1: Enqueue data until the FIFO is full
        $display("Test 1: Enqueue data until the FIFO is full");
        for (int i = 0; i < DEPTH; i++) begin
            #10;
            enq = 1;
            din = i;
        end
        enq = 0;
        #10;
        
        // Check if the FIFO is full
        if (full) begin
            $display("FIFO is full as expected.");
        end else begin
            $display("Error: FIFO is not full when it should be.");
        end

        // Test 2: Dequeue all data from the FIFO
        $display("Test 2: Dequeue all data from the FIFO");
        for (int i = 0; i < DEPTH; i++) begin
            #10;
            deq = 1;
            #10;
            $display("Read data: %d", dout);
        end
        deq = 0;
        #10;

        // Check if the FIFO is empty
        if (empty) begin
            $display("FIFO is empty as expected.");
        end else begin
            $display("Error: FIFO is not empty when it should be.");
        end

        // Test 3: Enqueue and dequeue operations interleaved
        $display("Test 3: Enqueue and dequeue operations interleaved");
        for (int i = 0; i < DEPTH/2; i++) begin
            #10;
            enq = 1;
            din = i;
            deq = 1;
            #10;
            $display("Read data: %d", dout);
        end
        enq = 0;
        deq = 0;
        #10;

        // Check final state of FIFO
        if (empty) begin
            $display("FIFO is empty as expected after interleaved operations.");
        end else begin
            $display("Error: FIFO is not empty when it should be after interleaved operations.");
        end

        // Finish simulation
        $display("Testbench completed.");
        $finish;
    end

endmodule