module tb_parameterized_counter;

    parameter WIDTH = 8;
    reg clk;
    reg reset;
    reg up;
    reg down;
    reg [WIDTH-1:0] init_val;
    wire [WIDTH-1:0] count;

    parameterized_counter #(WIDTH) uut (
        .clk(clk),
        .reset(reset),
        .up(up),
        .down(down),
        .init_val(init_val),
        .count(count)
    );

    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Test sequence
    initial begin
        // Initialize inputs
        reset = 0;
        up = 0;
        down = 0;
        init_val = 8'b00000010; // Initial value set to 2

        // Apply reset and initial value
        perform_reset(init_val);

        // Test up counting
        perform_up_count(10);

        // Test down counting
        perform_down_count(10);

        // Apply reset again with a different initial value
        perform_reset(8'b00000100); // Initial value set to 4

        // Test up counting again
        perform_up_count(10);

        // Finish simulation
        #50 $finish;
    end

    initial begin
        $monitor("At time %t, count = %h (up = %b, down = %b, reset = %b, init_val = %h)",
                 $time, count, up, down, reset, init_val);
    end

    // Task for performing reset
    task automatic perform_reset(input [WIDTH-1:0] init_value);
        begin
            init_val = init_value;
            reset = 1;
            #10 reset = 0;
        end
    endtask

    // Task for performing up count
    task automatic perform_up_count(input int count_cycles);
        begin
            up = 1;
            repeat (count_cycles) #10;
            up = 0;
        end
    endtask

    // Task for performing down count
    task automatic perform_down_count(input int count_cycles);
        begin
            down = 1;
            repeat (count_cycles) #10;
            down = 0;
        end
    endtask

endmodule
