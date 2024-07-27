// Test stimulus and scoreboard usage
initial begin
  // Initialize
  scoreboard = new();
  reset = 1;
  data_in = 8'h00;
  @(posedge clk);
  reset = 0;

  // Random test cases
  foreach (int i in {0:99}) begin
    data_in = $urandom_range(0, 255);
    scoreboard.add_expected(~data_in);
    @(posedge clk);
    scoreboard.compare_result(data_out);
  end

  // Edge cases
  data_in = 8'h00;
  scoreboard.add_expected(~8'h00);
  @(posedge clk);
  scoreboard.compare_result(data_out);

  data_in = 8'hFF;
  scoreboard.add_expected(~8'hFF);
  @(posedge clk);
  scoreboard.compare_result(data_out);

  // Report scoreboard statistics
  scoreboard.report_statistics();

  $finish;
end
