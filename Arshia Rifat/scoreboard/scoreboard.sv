class scoreboard #(parameter BIT_WIDTH = 8);
  // Internal storage
  bit [BIT_WIDTH-1:0] expected_results[$];
  int correct_count, error_count;

  // Initialize counters
  function new();
    correct_count = 0;
    error_count = 0;
  endfunction

  function void expect_result(bit [BIT_WIDTH-1:0] expected);
    expected_results.push_back(expected);
  endfunction

  // Verify actual output against expected
  function void check_output(bit [BIT_WIDTH-1:0] actual);
    bit [BIT_WIDTH-1:0] expected;

    if (expected_results.size() == 0) begin
      $error("Verification error: No more expected results in queue");
      return;
    end

    expected = expected_results.pop_front();

    if (actual === expected) begin
      correct_count++;
    end else begin
      error_count++;
      $display("Verification mismatch: expected %0h, Received %0h", expected, actual);
    end
  endfunction

  // Display verification summary
  function void print_summary();
    $display("Verification Summary:");
    $display("  Correct outputs: %0d", correct_count);
    $display("  Erroneous outputs: %0d", error_count);
    $display("  Remaining expected results: %0d", expected_results.size());
  endfunction
endclass