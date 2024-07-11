module tb_ALU16bit;


    reg [15:0] A;
    reg [15:0] B;
    reg [2:0] sel;


    wire [15:0] C;

    ALU16bit uut (
        .A(A),
        .B(B),
        .sel(sel),
        .C(C)
    );

    // Task to perform the test
    task perform_test(input [15:0] A_in, input [15:0] B_in, input [2:0] sel_in, input [15:0] expected);
        begin
            A = A_in;
            B = B_in;
            sel = sel_in;
            #10;
            if (C !== expected) begin
                $display("Test failed for A=%h, B=%h, sel=%b. Expected %h, got %h", A, B, sel, expected, C);
            end else begin
                $display("Test passed for A=%h, B=%h, sel=%b. Output %h", A, B, sel, C);
            end
        end
    endtask

    initial begin
        // Test ADD
        perform_test(16'h0001, 16'h0001, 3'b000, 16'h0002);
        perform_test(16'h00FF, 16'h0001, 3'b000, 16'h0100);

        // Test SUB
        perform_test(16'h0003, 16'h0001, 3'b001, 16'h0002);
        perform_test(16'h0100, 16'h000F, 3'b001, 16'h00F1);

        // Test AND
        perform_test(16'hFF00, 16'h0F0F, 3'b010, 16'h0F00);
        perform_test(16'hAAAA, 16'h5555, 3'b010, 16'h0000);

        // Test OR
        perform_test(16'hF0F0, 16'h0F0F, 3'b011, 16'hFFFF);
        perform_test(16'hAAAA, 16'h5555, 3'b011, 16'hFFFF);

        // Test XOR
        perform_test(16'hFFFF, 16'h0000, 3'b111, 16'hFFFF);
        perform_test(16'h1234, 16'h5678, 3'b111, 16'h444C);

        // Test default case
        perform_test(16'hAAAA, 16'h5555, 3'b100, 16'h0000);

        // End of test
        #10 $stop;
    end

    initial begin
        $monitor("At time %t, sel = %b, A = %h, B = %h, C = %h",
                 $time, sel, A, B, C);
    end

endmodule
