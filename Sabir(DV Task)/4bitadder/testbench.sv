`timescale 1ns / 1ps

module Adder4Bit_tb;
    // Inputs
    reg [3:0] A;
    reg [3:0] B;
    
    // Outputs
    wire [4:0] Sum;
    
    // Instantiate the Unit Under Test (UUT)
    Adder4Bit uut (
        .A(A), 
        .B(B), 
        .Sum(Sum)
    );
    
    // Variables for testing
    integer i, j;
    reg [4:0] expected_sum;

    initial begin
        // Initialize Inputs
        A = 0;
        B = 0;
        
        // Display headers
        $display("A     B     | Sum  | Expected Sum | Test Result");
        $display("===============================================");
        
        // Test all possible combinations of A and B
        for (i = 0; i < 16; i = i + 1) begin
            for (j = 0; j < 16; j = j + 1) begin
                A = i;
                B = j;
                expected_sum = i + j;
                #10; // Wait for the sum to be calculated
                // Check if the result is correct
                if (Sum == expected_sum)
                    $display("%4b  %4b  | %5b | %5b        | PASS", A, B, Sum, expected_sum);
                else
                    $display("%4b  %4b  | %5b | %5b        | FAIL", A, B, Sum, expected_sum);
            end
        end
        
        $finish;
    end
endmodule
