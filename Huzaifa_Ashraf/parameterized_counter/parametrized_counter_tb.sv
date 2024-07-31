module parametrized_counter_tb;

    parameter size = 8;
    reg up;
    reg down;
    reg reset;
    reg clk;
    reg [size-1:0] inp1;
    wire [size-1:0] count;

    // Instantiate parameterized_counter module
    parameterized_counter #(.size(size)) dut (
        .up(up),
        .down(down),
        .reset(reset),
        .clk(clk),
        .inp1(inp1),
        .count(count)
    );

    // Clock generation
    always #5 clk = ~clk;

    // Initial stimulus
    initial begin
        clk = 0;
        reset = 1;
        up = 0;
        down = 0;
        inp1 = 8'hAA;

        // Monitor output
        $monitor("Time=%t, up=%b, down=%b, count=%h", $time, up, down, count);

        // Release reset after some time
        #20 reset = 0;

        // Toggle up and down to observe count behavior
        #50 up = 1;
        #100 down = 1;
        #150 up = 0;
        #200 down = 0;

        

        // End simulation
        #250 $finish;
    end

endmodule
