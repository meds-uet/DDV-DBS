module counter_tb;
  // Parameters
  parameter size = 8;

  // Signals
  reg clk;
  reg reset;
  reg direction;
  reg [size-1:0] initial_value;
  wire [size-1:0] count;

  // Instantiate the counter
  counter #(size) uut (
    .clk(clk),
    .reset(reset),
    .direction(direction),
    .initial_value(initial_value),
    .count(count)
  );

  // Task to generate the clock
  task generate_clock;
    begin
      clk = 0;
      forever #5 clk = ~clk; // 10 time units period
    end
  endtask

  // Task to apply reset
  task apply_reset;
    input [size-1:0] init_value;
    begin
      reset = 1;
      initial_value = init_value;
      #20;
      reset = 0;
    end
  endtask

  // Task to test counting up
  task test_count_up;
    input int duration;
    begin
      direction = 1;
      #duration;
    end
  endtask

  // Task to test counting down
  task test_count_down;
    input int duration;
    begin
      direction = 0;
      #duration;
    end
  endtask

  // Initial block to apply the test cases
  initial begin
    // Open dump file for waveform analysis
    $dumpfile("counter_tb.vcd");
    $dumpvars(0, counter_tb);

    // Start clock generation
    fork
      generate_clock;
    join_none

    // Apply test cases
    apply_reset(8'h00);

    // Test counting up
    test_count_up(100); // Run for 100 time units

    // Test counting down
    test_count_down(100); // Run for 100 time units

    $stop; // Stop simulation
  end
endmodule