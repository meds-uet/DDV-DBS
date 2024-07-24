module tb_ALU_16bit;
    logic [15:0] A, B;
  	logic [2:0]  f_Sel;
    logic [15:0] Out;
    
    // Instantiate the ALU
    ALU_16bit uut (
        .A(A),
        .B(B),
     	.f_Sel(f_Sel),
        .Out(Out)
    );

    // Test task
    task test(input logic [15:0] a, 
              input logic [15:0] b, 
              input logic [2:0] sel, 
              input logic [15:0] expected);
        begin
            A = a;
            B = b;
            f_Sel = sel;
            #10; // wait for some time
            if (Out !== expected) begin
              $display("Test failed for f_Sel = %b, A = %h, B = %h. Expected %h but output %h", sel, a, b, expected, Out);
            end else begin
              $display("Test passed for f_Sel = %b, A = %h, B = %h. output %h", sel, a, b, Out);
            end
        end
    endtask

    initial begin
        // Test Case for addition
        test(16'h0001, 16'h0001, 3'b000, 16'h0002);
        test(16'hFFFF, 16'h0001, 3'b000, 16'h0000);

        // Test Case for subtraction
        test(16'h0002, 16'h0001, 3'b001, 16'h0001);
        test(16'h0000, 16'h0001, 3'b001, 16'hFFFF);

        // Test Case for AND
        test(16'hFFFF, 16'h0F0F, 3'b010, 16'h0F0F);
        test(16'hAAAA, 16'h5555, 3'b010, 16'h0000);

        // Test Case for OR
        test(16'hFFFF, 16'h0F0F, 3'b011, 16'hFFFF);
        test(16'hAAAA, 16'h5555, 3'b011, 16'hFFFF);

        // Test Case for XOR
        test(16'hFFFF, 16'h0F0F, 3'b100, 16'hF0F0);
        test(16'hAAAA, 16'h5555, 3'b100, 16'hFFFF);

        $stop;
    end
endmodule
