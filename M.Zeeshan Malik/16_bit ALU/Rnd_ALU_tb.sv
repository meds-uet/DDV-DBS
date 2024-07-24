module ALU_tb;

  reg [15:0] A;
  reg [15:0] B;
  reg [2:0] op;
  wire [15:0] result;

  ALU uut (
    .A(A),
    .B(B),
    .op(op),
    .result(result)
  );

  reg [15:0] expected_result;

  function [15:0] compute_expected_result(input [15:0] A, input [15:0] B, input [2:0] op);
    case(op)
      3'b000: compute_expected_result = A + B;
      3'b001: compute_expected_result = A - B;
      3'b010: compute_expected_result = A & B;
      3'b011: compute_expected_result = A | B;
      3'b100: compute_expected_result = A ^ B;
      default: compute_expected_result = 16'b0;
    endcase
  endfunction

  initial begin
    repeat (1000) begin
      A = $random;
      B = $random;
      op = $random % 5;

     
      expected_result = compute_expected_result(A, B, op);

      #1;

     
      assert (result == expected_result) else $fatal("Test failed: A=%h, B=%h, op=%b, result=%h, expected_result=%h", A, B, op, result, expected_result);
      
      #1;
    end

    $display("All tests passed!");
    $finish;
  end

endmodule
