class Scoreboard #(parameter DATA_WIDTH = 8);
  bit [DATA_WIDTH-1:0] expected_queue[$];
  int match_count, mismatch_count;

  // Constructor
  function new();
    match_count = 0;
    mismatch_count = 0;
  endfunction


  function void add_expected(input bit [DATA_WIDTH-1:0] expected);
    expected_queue.push_back(expected);
  endfunction
  
  
 bit [DATA_WIDTH-1:0] expected;

  function void compare_result(input bit [DATA_WIDTH-1:0] actual);
    if (expected_queue.size() == 0) begin
      $error("No expected data in queue to compare.");
      return;
    end

     expected = expected_queue.pop_front();

    if (actual === expected) begin
      match_count++;
    end else begin
      mismatch_count++;
      $error("Mismatch: Expected %0h, got %0h", expected, actual);
    end
  endfunction


  function void report_statistics();
    $display("Scoreboard Statistics:");
    $display("  Matches: %0d", match_count);
    $display("  Mismatches: %0d", mismatch_count);
    $display("  Items left in queue: %0d", expected_queue.size());
  endfunction
endclass
