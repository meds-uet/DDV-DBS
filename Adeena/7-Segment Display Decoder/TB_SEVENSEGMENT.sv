module tb_bin_to_7segment;

    logic [3:0] bin;      
    logic [6:0] seg;       
    logic [6:0] expected;  // Expected segment output

    // Instantiate the Unit Under Test (UUT)
    bin_to_7segment uut (
        .bin(bin),
        .seg(seg)
    );

    // Test vector array
    logic [6:0] expected_segments [15:0];

    // Initialize the test vectors
    initial begin
        expected_segments[0]  = 7'b0111111; // 0
        expected_segments[1]  = 7'b0000110; // 1
        expected_segments[2]  = 7'b1011011; // 2
        expected_segments[3]  = 7'b1001111; // 3
        expected_segments[4]  = 7'b1100110; // 4
        expected_segments[5]  = 7'b1101101; // 5
        expected_segments[6]  = 7'b1111101; // 6
        expected_segments[7]  = 7'b0000111; // 7
        expected_segments[8]  = 7'b1111111; // 8
        expected_segments[9]  = 7'b1101111; // 9
        expected_segments[10] = 7'b1110111; // A
        expected_segments[11] = 7'b1111100; // B
        expected_segments[12] = 7'b0111001; // C
        expected_segments[13] = 7'b1011110; // D
        expected_segments[14] = 7'b1111001; // E
        expected_segments[15] = 7'b1110001; // F
    end

    // Task to perform the test
    task perform_test(input [3:0] bin_in, input [6:0] expected_in);
        begin
            bin = bin_in;
            expected = expected_in;
            #10;
            if (seg !== expected) begin
                $display("Test failed for input %b. Expected %b, got %b", bin, expected, seg);
            end else begin
                $display("Test passed for input %b. Output %b", bin, seg);
            end
        end
    endtask

    // Testbench logic
    initial begin
        for (int i = 0; i < 16; i++) begin
            perform_test(i, expected_segments[i]);
        end

        $display("All tests completed.");
        $finish;
    end

endmodule
