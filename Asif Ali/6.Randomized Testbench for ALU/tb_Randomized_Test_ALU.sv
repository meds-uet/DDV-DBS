`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/29/2024 08:00:11 PM
// Design Name: 
// Module Name: tb_Randomized_Test_ALU
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

module tb_Randomized_Test_ALU;

    // Testbench signals
    logic [15:0] a, b;
    logic [3:0]  op;
    logic [15:0] result;
    logic        zero, carry, overflow;

    Randomized_Tezt_ALU uut (
        .a(a),
        .b(b),
        .op(op),
        .result(result),
        .zero(zero),
        .carry(carry),
        .overflow(overflow)
    );

    logic        expected_zero, expected_carry, expected_overflow;

    task generate_random_test;
        logic [15:0] expected_result;
        logic        expected_carry_temp;
        logic        expected_overflow_temp;

        // Generate random values for inputs
        a = $random;
        b = $random;
        op = $random % 8;  

        case(op)
            4'b0000: begin  // Addition
                expected_result = a + b;
                expected_carry_temp = (a + b) > 16'hFFFF;;
                expected_overflow_temp = ((a[15] == b[15]) && (expected_result[15] != a[15]));
            end
            4'b0001: begin  // Subtraction
                expected_result = a - b;
                expected_carry_temp = (a < b);  
                expected_overflow_temp = ((a[15] != b[15]) && (expected_result[15] != a[15]));
            end
            4'b0010: expected_result = a & b;  // AND
            4'b0011: expected_result = a | b;  // OR
            4'b0100: expected_result = a ^ b;  // XOR
            4'b0101: expected_result = ~a;     // NOT
            4'b0110: expected_result = a << 1; // Shift left
            4'b0111: expected_result = a >> 1; // Shift right
            default: expected_result = 16'h0000;
        endcase

        // Compute zero flag
        expected_zero = (expected_result == 16'h0000);
        expected_carry = expected_carry_temp;
        expected_overflow = expected_overflow_temp;

        #20;  

        assert(result == expected_result) else $fatal("Error: result mismatch: expected %h, got %h", expected_result, result);
        assert(zero == expected_zero) else $fatal("Error: zero flag mismatch: expected %b, got %b", expected_zero, zero);
        
        $display("time: %d, op: %b, a: %h, b: %h, result: %h, expected_result: %h", $time, op, a, b, result, expected_result);
    endtask

    initial begin
        for (int i = 0; i < 1000; i++) begin
            generate_random_test();
        end
        $display("All tests passed.");
        $finish;
    end

endmodule
