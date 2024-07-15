module tb_level_to_pulse_converter;
    // Testbench signals
    logic clk;
    logic reset;
    logic X;
    logic Y;

    // Instantiate the DUT
    level_to_pulse_converter uut (
        .clk(clk),
        .reset(reset),
        .X(X),
        .Y(Y)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns period clock
    end

    // Driver task to apply input pulse
    task apply_pulse(input integer width);
        begin
            X = 1;
            repeat (width) @(posedge clk);
            X = 0;
            repeat (width) @(posedge clk);
        end
    endtask

    // Monitor task to check the output
    task monitor;
        logic prev_X;
        logic prev_Y;

        begin
            prev_X = X;
            prev_Y = Y;

            @(posedge clk); // Wait for the first clock edge

            forever begin
                @(posedge clk);
                if ((prev_X != X) && (prev_Y != Y)) begin
                    $display("Pass: Change in input X detected, output Y changed.");
                end else if ((prev_X == X) && (prev_Y != Y)) begin
                    $display("Fail: Output Y changed without change in input X.");
                end else if ((prev_X != X) && (prev_Y == Y)) begin
                    $display("Fail: Input X changed but output Y did not change.");
                end
                prev_X = X;
                prev_Y = Y;
            end
        end
    endtask

    // Initial block to reset and apply test vectors
    initial begin
        reset = 1;
        X = 0;
        #15;
        reset = 0;

        fork
            monitor();
            begin
                for (int i = 1; i <= 5; i++) begin
                    apply_pulse(i); // Apply pulse with width i clock periods
                end
                #20;
                $stop;
            end
        join
    end

endmodule
