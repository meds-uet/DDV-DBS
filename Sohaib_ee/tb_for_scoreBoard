include "scoreboard.sv";

module tb_for_scoreBoard;
  logic clk, reset;
  logic [7:0] data_in, data_out;
  logic invert;

  Inverter uut (
    .clk(clk),
    .reset(reset),
    .data_in(data_in),
    .data_out(data_out),
    .invert(invert)
  );

  // Instantiate Scoreboard
  Scoreboard #(.DATA_WIDTH(8)) scoreboard;

  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  initial begin
    // Initialize
    scoreboard = new();
    reset = 1;
    data_in = 8'h00;
    invert = 0;
    @(posedge clk);
    reset = 0;

    // Test case 1: Simple data pass-through
    @(posedge clk);
    data_in = 8'hAA; // Input data
    scoreboard.add_expected(8'hAA); // Expected output
    @(posedge clk);
    scoreboard.compare_result(data_out);

    // Test case 2: Data inversion
    invert = 1;
    @(posedge clk);
    data_in = 8'h55; 
    scoreboard.add_expected(8'hAA); 
    @(posedge clk);
    scoreboard.compare_result(data_out);


    scoreboard.report_statistics();

    $finish;
  end
endmodule
