`include "scoreboard.sv"

module dut_tb;
  // DUT signals
  logic clk, reset;
  logic [7:0] data_in, data_out;
  logic mode;

  // Instantiate DUT
  dut uut (
    .clk(clk),
    .reset(reset),
    .data_in(data_in),
    .data_out(data_out),
    .mode(mode)
  );

  Scoreboard #(.DATA_WIDTH(8)) scoreboard;

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  initial begin
    scoreboard = new();
    reset = 1;
    data_in = 8'h00;
    mode = 0;
    @(posedge clk);
    reset = 0;

    // Corner cases
    data_in = 8'h00; // all zeros
    mode = 0;
    scoreboard.add_expected(8'h00);
    @(posedge clk);
    scoreboard.compare_result(data_out);

    data_in = 8'hFF; // all ones
    mode = 1;
    scoreboard.add_expected(~8'hFF);
    @(posedge clk);
    scoreboard.compare_result(data_out);

    data_in = 8'hAA; // alternating bits
    mode = 0;
    scoreboard.add_expected(8'hAA);
    @(posedge clk);
    scoreboard.compare_result(data_out);

    data_in = 8'h55; // alternating bits
    mode = 1;
    scoreboard.add_expected(~8'h55);
    @(posedge clk);
    scoreboard.compare_result(data_out);

    // Random test cases
    for (int i = 0; i < 100; i++) begin
      data_in = $urandom();
      mode = $urandom() % 2;
      if (mode == 0) begin
        scoreboard.add_expected(data_in);
      end else begin
        scoreboard.add_expected(~data_in);
      end
      @(posedge clk);
      scoreboard.compare_result(data_out);
    end

    // Report scoreboard statistics
    scoreboard.report_statistics();

    $finish;
  end

    initial begin
        $dumpfile("scoreboard.vcd");
        $dumpvars(0,dut_tb);
    end
endmodule
