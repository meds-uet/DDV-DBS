module alu_16b_tb;

    logic [15:0] a_i, b_i;
    logic [2:0]  alu_ctrl_i;
    logic [16:0] c_o;
    logic [16:0] c_expected;

    parameter int TEST_SIZE = 100; 
    int correct_check = 0;
    int incorrect_check = 0;
    int total_checks = 0;

    // Individual operation counters
    int add_correct = 0, add_incorrect = 0;
    int sub_correct = 0, sub_incorrect = 0;
    int and_correct = 0, and_incorrect = 0;
    int or_correct = 0, or_incorrect = 0;
    int xor_correct = 0, xor_incorrect = 0;

    alu_16b dut (.a_i(a_i), .b_i(b_i), .alu_ctrl_i(alu_ctrl_i), .c_o(c_o));

    // Task to generate stimulus
    task generator_task(input int test_num, input logic [2:0] alu_ctrl);
        string operation;
        begin
            a_i = $urandom;
            b_i = $urandom;
            case (alu_ctrl)
                3'b000: begin
                    c_expected = a_i + b_i;
                    operation = "ADD";
                end
                3'b001: begin
                    c_expected = a_i - b_i;
                    operation = "SUB";
                end
                3'b010: begin
                    c_expected = a_i & b_i;
                    operation = "AND";
                end
                3'b011: begin
                    c_expected = a_i | b_i;
                    operation = "OR";
                end
                3'b100: begin
                    c_expected = a_i ^ b_i;
                    operation = "XOR";
                end
                default: begin
                    c_expected = a_i + b_i;
                    operation = "DEFAULT (ADD)";
                end
            endcase
            $display("Test %d: Operation = %s, a = %d, b = %d, expected = %d", test_num, operation, a_i, b_i, c_expected);
        end
    endtask

    // Task to monitor and check results
    task monitor_task(input int test_num, input logic [2:0] alu_ctrl);
        string operation;
        begin
            #10; // Wait for some time to simulate the delay
            case (alu_ctrl)
                3'b000: operation = "ADD";
                3'b001: operation = "SUB";
                3'b010: operation = "AND";
                3'b011: operation = "OR";
                3'b100: operation = "XOR";
                default: operation = "DEFAULT (ADD)";
            endcase

            if (c_o == c_expected) begin
                $display("Check %d -> Passed: Operation = %s, a = %d, b = %d, c = %d, expected = %d", test_num, operation, a_i, b_i, c_o, c_expected);
                correct_check++;
                case (alu_ctrl)
                    3'b000: add_correct++;
                    3'b001: sub_correct++;
                    3'b010: and_correct++;
                    3'b011: or_correct++;
                    3'b100: xor_correct++;
                endcase
            end else begin
                $display("Check %d -> Failed: Operation = %s, a = %d, b = %d, c = %d, expected = %d", test_num, operation, a_i, b_i, c_o, c_expected);
                incorrect_check++;
                case (alu_ctrl)
                    3'b000: add_incorrect++;
                    3'b001: sub_incorrect++;
                    3'b010: and_incorrect++;
                    3'b011: or_incorrect++;
                    3'b100: xor_incorrect++;
                endcase
            end
            total_checks++;
        end
    endtask

    initial begin
        for (alu_ctrl_i = 0; alu_ctrl_i < 5; alu_ctrl_i++) begin
            for (int i = 0; i < TEST_SIZE; i++) begin
                generator_task(i, alu_ctrl_i);
                monitor_task(i, alu_ctrl_i);
            end
        end
        $display("Total checks: %d, Passed: %d, Failed: %d", total_checks, correct_check, incorrect_check);
        $display("Operation-wise results:");
        $display("ADD Passed: %d, Failed: %d", add_correct, add_incorrect);
        $display("SUB Passed: %d, Failed: %d", sub_correct, sub_incorrect);
        $display("AND Passed: %d, Failed: %d", and_correct, and_incorrect);
        $display("OR Passed: %d, Failed: %d", or_correct, or_incorrect);
        $display("XOR Passed: %d, Failed: %d", xor_correct, xor_incorrect);
    end

    initial begin
        $dumpfile("alu_16b_tb.vcd");
        $dumpvars(0, alu_16b_tb);
    end

endmodule

