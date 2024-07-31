module tb_level_to_pulse_converter;
    logic clk;
    logic reset;
    logic X;
    logic out;

    level_to_pulse_converter uut (
        .clk(clk),
        .reset(reset),
        .X(X),
        .out(out)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; 
    end

    // Initialize waveform dump
    initial begin
        $dumpfile("tb_level_to_pulse_converter.vcd");
        $dumpvars(0, tb_level_to_pulse_converter);
    end

    // Test stimulus
    initial begin
        reset = 1;
        X = 0;
        #15;
        reset = 0;

        fork
            monitor();
            begin
                for (int i = 1; i <= 10; i++) begin
                    apply_pulse(i); 
                end
                #50;
                $finish;
            end
        join
    end

    // Driver task to apply input pulse
    task apply_pulse(input integer w);
        begin
            X = 1;
            repeat (w) @(posedge clk);
            X = 0;
            repeat (w) @(posedge clk);
        end
    endtask

    // Monitor task to check the output
      task monitor;
        logic prev_X;
        prev_X = 0;
        forever begin
                @(posedge clk);     // WAIT FOR 1 CLOCK EDGE TO DETECTT THE OUTPUT ;
                if ((X==1) && (prev_X== 0)) begin
                    prev_X = X;
                    @(posedge clk);
                    prev_X = X;
                    if (out == 0) begin
                    $display("failed.");
                    end
                else 
                begin
                    prev_X = X;
                    @(posedge clk);
                    prev_X = X;
                    if (out ==1) begin
                        $display("failed.");
                    end
                end
                prev_X = X;
            end
        end
    endtask

    // Assertion for pulse generation
    sequence pulse_gen;
        @(posedge clk) (X && !reset) ##1 (!X && out) ##1 (out == 0);
    endsequence

    property pulse_property;
        disable iff (!reset)
        pulse_gen;
    endproperty

    assert property (pulse_property)
    else $fatal("Assertion failed: Pulse generation error");

endmodule
