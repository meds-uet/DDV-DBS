`include "scoreboard.sv"

module tb_dut;
  // DUT signals
  logic clk, reset;
  logic [7:0] data_in, data_out;

  // Instantiate DUT
  dut uut (
    .clk(clk),
    .reset(reset),
    .data_in(data_in),
    .data_out(data_out)
  );

  // Instantiate Scoreboard
  Scoreboard #(.DATA_WIDTH(8)) scoreboard;

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
    data_in = 8'h00;
    @(posedge clk);
    reset = 0;

    // Test case 1: Simple data pass-through
    data_in = 8'hA5;
    scoreboard.add_expected(~8'hA5);
    @(posedge clk);
    scoreboard.compare_result(data_out);

    // Test case 2: Another data inversion
    data_in = 8'h5A;
    scoreboard.add_expected(~8'h5A);
    @(posedge clk);
    scoreboard.compare_result(data_out);

    // Add more test cases here...

    // Report scoreboard statistics
    scoreboard.report_statistics();

    $finish;
  end
endmodule
