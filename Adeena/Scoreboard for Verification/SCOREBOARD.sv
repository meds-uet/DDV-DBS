class Scoreboard #(parameter DATA_WIDTH = 8);
  // Internal data structures
  bit [DATA_WIDTH-1:0] expected_queue[$];
  int match_count, mismatch_count;

  // Constructor to initialize counts
  function new();
    match_count = 0;
    mismatch_count = 0;
  endfunction

  function void add_expected(bit [DATA_WIDTH-1:0] expected);
      expected_queue.push_back(expected);
    endfunction

  // Method to compare actual result with expected
  function void compare_result(bit [DATA_WIDTH-1:0] actual);
     bit [DATA_WIDTH-1:0] expected;

    if (expected_queue.size() == 0) begin
      $error("No more expected results in queue to compare");
      return;
    end

    expected = expected_queue.pop_front();

    
    if (actual === expected) begin
      match_count ++ ;
    end else begin
      mismatch_count ++ ;
      $display("Mismatch error: Expected %0h, got %0h", expected, actual);
    end
  endfunction

 
  function void report_statistics();
    $display("Scoreboard Statistics:");
    $display("  Matches: %0d", match_count);
    $display("  Mismatches: %0d", mismatch_count);
    $display("  Items left in queue: %0d", expected_queue.size());
  endfunction
endclass