
` include "sb_sb.sv"
module tb_dut;
  // DUT signals
  logic clk, reset;
  //logic [15:0] data_in, data_out;
  logic [15:0] a, b, out;
  logic [2:0] sel;

  // TODO: Instantiate DUT
  alu_design uut(
  .a(a),
  .b(b),
  .sel(sel),
  .out(out)
  );
  // TODO: Instantiate Scoreboard
   scoreboard #(.DATA_WIDTH(16)) scoreboard;

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
    //data_in = 16'h00f;
    @(posedge clk);
    reset = 0;

    // TODO: Test case 1: Simple data pass-through
    a = 16'h123;
    b = 16'h456;
    sel = 3'b000; // a + b
    #10;
    scoreboard.add_expected(16'h0579); // Expected result for a + b
    scoreboard.compare_result(out);
#10

    a = 16'h123;
    b = 16'h456;
    sel = 3'b000; // a + b
    #10;
    scoreboard.add_expected(16'h0578); // Expected result for a + b
    scoreboard.compare_result(out);

    // TODO: Test case 2: Data inversion (assuming DUT inverts data)

    // Add more test cases here...

    // Report scoreboard statistics
    scoreboard.report_statistics();

    $finish;
  end
endmodule


