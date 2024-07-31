module tb_FIFO();

    // Parameters
    parameter Width = 4;
    parameter Depth = 4;

    // Signals
    logic [Width-1:0] Data_in;
    logic [Width-1:0] Data_out;
    logic push, pop;
    logic full, empty;
    logic clk, reset, w_en, r_en;

    // Instantiate FIFO module
    FIFO #(
        .Width(Width),
        .Depth(Depth)
    ) dut (
        .Data_in(Data_in),
        .push(push),
        .pop(pop),
        .Data_out(Data_out),
        .full(full),
        .empty(empty),
        .clk(clk),
        .reset(reset),
        .w_en(w_en),
        .r_en(r_en)
    );

    // Clock generation
    always begin
        clk = 0;
        #5; // Adjust delay as needed
        clk = 1;
        #5; // Adjust delay as needed
    end

    // Initial stimulus and reset
    initial begin
        reset = 1;
        w_en = 0;
        r_en = 0;
        push = 0;
        pop = 0;
        Data_in = 0;

        // Wait for some time for reset to stabilize
        #20;

        // Release reset
        reset = 0;
        
        // Example test scenario
        // Writing data to FIFO
        push = 1;
        Data_in = 4'b1101; // Example data
        w_en = 1;
        #10; // Allow time for write operation
        
        // Reading data from FIFO
        r_en = 1;
        #30; // Allow time for read operation

        // Additional test cases can be added here

        // End simulation after test cases
        $finish;
    end

    // Monitor for observing outputs (optional)
    always @(posedge clk) begin
        $display("Time=%0t: Data_out=%h, full=%b, empty=%b", $time, Data_out, full, empty);
    end

endmodule