module parameterized_counter_tb;

    parameter WIDTH = 8;

    logic clk;
    logic reset;
    logic enable;
    logic up_down;
    logic [WIDTH-1:0] init_value;
    logic [WIDTH-1:0] count;

    // Instantiating the counter
    parameterized_counter #(
        .WIDTH(WIDTH)
    ) uut (
        .clk(clk),
        .reset(reset),
        .enable(enable),
        .up_down(up_down),
        .init_value(init_value),
        .count(count)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; 
    end

    // Stimulus
    initial begin
        reset = 1;
        enable = 0;
        up_down = 1;
        init_value = 8'h55;
        #20;
        reset = 0;
        enable = 1;
        #100;
        enable = 0;
        #20;

        // Testing count down
        up_down = 0;
        enable = 1;
        #100;
        enable = 0;
        #20;

        // Testing reset
        reset = 1;
        #20;
        reset = 0;
        #100;

        // Testing with a different initial value
        init_value = 8'hAA; 
        reset = 1;
        #20;
        reset = 0;
        enable = 1;
        up_down = 1;
        #100;
        enable = 0;
        #20;

        $stop;
    end

    // Monitor for count value
    initial begin
        $monitor("Time = %0t, Reset = %b, Enable = %b, Up_Down = %b, Count = %0d", $time, reset, enable, up_down, count);
        $dumpfile("counter.vcd");
        $dumpvars(0,parameterized_counter_tb);
    end

endmodule
