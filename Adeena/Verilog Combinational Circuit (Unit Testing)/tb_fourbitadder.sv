`timescale 1ns / 1ps

module tb_four_bit_adder;

    // Inputs
    reg [3:0] a;
    reg [3:0] b;

    // Outputs
    wire [4:0] sum;

    // Variables
    logic [4:0] expected_sum;

    // Instantiate the Unit Under Test (UUT)
    four_bit_adder uut (
        .a(a), 
        .b(b), 
        .sum(sum)
    );

    // Task to perform addition and check result
    task perform_test(input [3:0] a_in, input [3:0] b_in);
        begin
            a = a_in;
            b = b_in;
            #10;
            expected_sum = a + b;
            if (sum === expected_sum) begin
                $display("%0d | %b | %b | %b | %b          | Pass", $time, a, b, sum, expected_sum);
            end else begin
                $display("%0d | %b | %b | %b | %b          | Fail", $time, a, b, sum, expected_sum);
            end
        end
    endtask

    // Testbench logic
    initial begin
        // Display header for the test results
        $display("Time | a     | b     | sum  | Expected Sum | Pass/Fail");
        $display("-----|-------|-------|------|--------------|----------");

        for (int i = 0; i < 16; i = i + 1) begin
            for (int j = 0; j < 16; j = j + 1) begin
                perform_test(i, j);
            end
        end

        $stop;
    end

endmodule
