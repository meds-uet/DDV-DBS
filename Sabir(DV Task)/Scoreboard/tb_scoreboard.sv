`include "scoreboard.sv"

module tb_4bit_adder;
  // DUT signals
  logic clk, reset;
  logic [3:0] a, b;
  logic [3:0] sum;
  logic carry_out;

  // Instantiate DUT
  adder_4bit dut (
    .a(a),
    .b(b),
    .sum(sum),
    .carry_out(carry_out)
  );

  // Instantiate Scoreboard
  Scoreboard #(.DATA_WIDTH(4)) scoreboard;

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Test stimulus and scoreboard usage
  initial begin
    // Initialize
    scoreboard = new();
    reset = 1;
    a = 4'h0;
    b = 4'h0;
    @(posedge clk);
    reset = 0;

    // Test case 1: Add 2 + 3
    a = 4'h2;
    b = 4'h3;
    #10;
    scoreboard.add_expected(5); // 2 + 3 = 5
    scoreboard.compare_result({carry_out, sum});

    // Test case 2: Add 7 + 8
    a = 4'h7;
    b = 4'h8;
    #10;
    scoreboard.add_expected(15); // 7 + 8 = 15
    scoreboard.compare_result({carry_out, sum});

    // Additional test cases can be added here...

    // Report scoreboard statistics
    scoreboard.report_statistics();

    $finish;
  end
endmodule
