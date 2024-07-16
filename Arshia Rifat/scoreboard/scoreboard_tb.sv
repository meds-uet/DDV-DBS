`include "fifo_scoreboard.svh"
`include "scoreboard.sv"
`include "ref_alu.sv"

module testbench_fifo;
  // Parameters
  parameter BIT_WIDTH = 8;
  parameter FIFO_DEPTH = 16;

  // DUT signals
  logic clock, reset;
  logic write_enable, read_enable;
  logic [BIT_WIDTH-1:0] write_data, read_data;
  logic fifo_empty, fifo_full;
  logic [7:0] operand_a, operand_b;
  logic [BIT_WIDTH-1:0] fifo_output;
  logic [2:0] operation;
  logic [7:0] alu_result;
  
  // ALU reference model
  ALU_reference alu_ref (
    .A(operand_a),
    .B(operand_b),
    .op(operation),
    .result_expected(alu_result)
  );

  // DUT instantiation
  FIFO #(BIT_WIDTH, FIFO_DEPTH) dut (
    .clock(clock),
    .reset(reset),
    .write_enable(write_enable),
    .read_enable(read_enable),
    .write_data(alu_result),
    .read_data(read_data),
    .fifo_empty(fifo_empty),
    .fifo_full(fifo_full)
  );

  // Result scoreboard instantiation
  scoreboard #(BIT_WIDTH) scoreboard;

  // Clock generation
  initial begin
    clock = 0;
    forever #5 clock = ~clock;
  end

  // Test sequence
  initial begin
    reset = 1;
    #10;
    reset = 0;
    scoreboard = new();

    // Test ALU operations and FIFO
    //Test case 1:
    operand_a = 8'h12;
    operand_b = 8'h34;
    operation = 3'b000; // Addition

    @(posedge clock);
    scoreboard.expect_result(alu_result);
    write_enable = 1; read_enable = 0; write_data = alu_result;
    @(posedge clock);
    write_enable = 0; read_enable = 1;
    @(posedge clock);
    fifo_output = read_data;
    #10 scoreboard.check_output(fifo_output);

    //Test case 2:
    operand_a = 8'h56;
    operand_b = 8'h78;
    operation = 3'b001; // Subtraction

    @(posedge clock);
    scoreboard.expect_result(alu_result);
    write_enable = 1; read_enable = 0; write_data = alu_result;
    @(posedge clock);
    write_enable = 0; read_enable = 1;
    @(posedge clock);
    fifo_output = read_data;
    #10 scoreboard.check_output(fifo_output);

    //Test case 3:
    operand_a = 8'hA5;
    operand_b = 8'h5A;
    operation = 3'b010; // Bitwise AND

    @(posedge clock);
    scoreboard.expect_result(alu_result);
    write_enable = 1; read_enable = 0; write_data = alu_result;
    @(posedge clock);
    write_enable = 0; read_enable = 1;
    @(posedge clock);
    fifo_output = read_data;
    #10 scoreboard.check_output(fifo_output);
    scoreboard.print_summary();

    $finish;
  end
endmodule