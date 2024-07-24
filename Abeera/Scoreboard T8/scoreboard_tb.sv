`include "fifo_scoreboard.svh"
`include "scoreboard.sv"

module tb_fifo;

  // Parameters
  parameter DATA_WIDTH = 8;
  parameter DEPTH = 16;

  // DUT signals
  logic clk, rst;
  logic wr_en, rd_en;
  logic [DATA_WIDTH-1:0] wr_data, rd_data;
  logic empty, full;
  logic [7:0] A, B;
  logic [DATA_WIDTH-1:0] rd1_data;
  logic [2:0] op;
  logic [7:0] result;
  
  // Instantiate ALU reference model
  ALU_ref uut_ALU_ref (
    .A(A),
    .B(B),
    .op(op),
    .result_expected(result)
  );

  // DUT instantiation
  FIFO #(DATA_WIDTH, DEPTH) dut (
    .clk(clk),
    .rst(rst),
    .wr_en(wr_en),
    .rd_en(rd_en),
    .wr_data(result),
    .rd_data(rd_data),
    .empty(empty),
    .full(full)
  );

  // Scoreboard instantiation
  Scoreboard #(DATA_WIDTH) scoreboard;  // Instantiate the Scoreboard

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Tasks for driving, monitoring, and predicting
  task driver(input logic wr_en_in, input logic rd_en_in, input logic [DATA_WIDTH-1:0] data);
    wr_en = wr_en_in;
    rd_en = rd_en_in;
    wr_data = data;
    @(posedge clk);
  endtask

  task monitor(output logic [DATA_WIDTH-1:0] data);
    @(posedge clk);
    data = rd_data;
  endtask

  task predictor(input logic [DATA_WIDTH-1:0] data);
    logic [DATA_WIDTH-1:0] expected;
    expected = data;
    scoreboard.add_expected(expected);
  endtask

  // Test sequence
  initial begin
    rst = 1;
    #10;
    rst = 0;
    scoreboard = new();
    // Test ALU operations and FIFO
    // Example operation
    A = 8'h12;
    B = 8'h34;
    op = 3'b000; // Assume this is an addition operation

    // Generate result from ALU
    @(posedge clk);
    predictor(result); // Add expected result to the scoreboard
    driver(1, 0, result); // Write ALU result to FIFO
    @(posedge clk);
    driver(0, 1, 8'h00); // Read from FIFO
    @(posedge clk);
    monitor(rd1_data); // Capture the data read from FIFO
    #10 scoreboard.compare_result(rd1_data); // Compare with expected result


    // Additional ALU operations and FIFO interactions
    A = 8'h56;
    B = 8'h78;
    op = 3'b001; // Assume this is a subtraction operation

    // Generate result from ALU
    @(posedge clk);
    predictor(8'hde); // Add expected result to the scoreboard
    driver(1, 0, result); // Write ALU result to FIFO
    @(posedge clk);
    driver(0, 1, 8'h00); // Read from FIFO
    @(posedge clk);
    monitor(rd1_data); // Capture the data read from FIFO
    #10 scoreboard.compare_result(rd1_data); // Compare with expected result

    // Additional test cases
    // Add more test cases as needed, following the same pattern

    // Report scoreboard statistics
    scoreboard.report_statistics();

    $finish;
  end
endmodule
