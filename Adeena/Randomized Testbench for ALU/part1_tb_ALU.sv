`timescale 1ns / 1ps

module tb_ALU16bit_part1;

  // ALU inputs
  reg [15:0] A, B;
  reg [2:0] sel;
  reg clk;
  
  // ALU output
  wire [15:0] C;
  
  // Instantiate the ALU
  ALU16bit uut (
    .A(A),
    .B(B),
    .sel(sel),
    .C(C)
  );
  
  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end
  
  // Task to apply random inputs
  task apply_random_inputs;
    begin
      A = $random;
      B = $random;
      sel = $random % 8;  
    end
  endtask
  
  // Expected result calculation
  function [15:0] calculate_expected_result;
    input [15:0] A, B;
    input [2:0] sel;
    reg [15:0] result;
    begin
      case (sel)
        3'b000: result = A + B;  // Addition
        3'b001: result = A - B;  // Subtraction
        3'b010: result = A & B;  // AND
        3'b011: result = A | B;  // OR
        3'b111: result = A ^ B;  // XOR
        default: result = 16'b0;
      endcase
      calculate_expected_result = result;
    end
  endfunction
  
  // Testbench logic
  initial begin
    // Apply random inputs and check outputs
    repeat (100) begin  // Adjust the repeat count as needed
      apply_random_inputs;
      #10;
      assert(C === calculate_expected_result(A, B, sel)) else
        $fatal("C mismatch: Expected %h, Got %h", calculate_expected_result(A, B, sel), C);
    end
    $display("All tests passed.");
    $finish;
  end

endmodule
