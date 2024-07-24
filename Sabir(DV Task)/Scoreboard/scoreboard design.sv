class Scoreboard #(parameter DATA_WIDTH = 4); // 4-bit data width for the adder
  // Internal data structures
  bit [DATA_WIDTH:0] expected_queue[$]; // Extra bit for carry-out
  int match_count, mismatch_count;

  // Constructor
  function new();
    match_count = 0;
    mismatch_count = 0;
  endfunction

  // Method to add expected result
  function void add_expected(bit [DATA_WIDTH:0] expected); // Extra bit for carry-out
    expected_queue.push_back(expected);
  endfunction

  // Method to compare actual result with expected
  function void compare_result(bit [DATA_WIDTH:0] actual); // Extra bit for carry-out
    if (expected_queue.size() == 0) begin
      $error("No expected results in queue to compare!");
      return;
    end

    bit [DATA_WIDTH:0] expected = expected_queue.pop_front();

    if (actual === expected) begin
      match_count++;
    end else begin
      mismatch_count++;
      $error("Mismatch! Expected: %b, Actual: %b", expected, actual);
    end
  endfunction

  // Method to display scoreboard statistics
  function void report_statistics();
    $display("Scoreboard Statistics:");
    $display("  Matches: %0d", match_count);
    $display("  Mismatches: %0d", mismatch_count);
    $display("  Items left in queue: %0d", expected_queue.size());
  endfunction
endclass

