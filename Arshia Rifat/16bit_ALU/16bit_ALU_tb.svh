module 16bit_ALU_tb;
    reg [15:0] in1, in2;
    reg [2:0] control;
    wire [15:0] out;

    t1e3 uut (
        .in1(in1),
        .in2(in2),
        .control(control),
        .out(out)
    );


    initial begin
        // ADD
        in1 = 16'h1234; in2 = 16'h5678; control = 3'b000; 
        #10;
        if (out !== 16'h68AC) begin
            $display("ERROR: Addition failed! Expected %h, got %h", 16'h68AC, out);
        end
        //SUB
        in1 = 16'h9397; in2 = 16'h8356; control = 3'b001; 
        #10;
      if (out !== 16'h1041) begin
            $display("ERROR: Subtraction failed! Expected %h, got %h", 16'h43E4, out);
          
        end

        // AND
        in1 = 16'hff00; in2 = 16'h0f0f; control = 3'b010; 
        #10;
      if (out !== 16'h0f00) begin
            $display("ERROR: AND operation failed! Expected %h, got %h", 16'hA0C0, out);
           
        end
        //OR
        in1 = 16'hf0f0; in2 = 16'h0f0f; control = 3'b011; 
        #10;
      if (out !== 16'hffff) begin
        $display("ERROR: OR operation failed! Expected %h, got %h", 16'hffff, out);
           
        end
    //XOR
        in1 = 16'hffff; in2 = 16'h0000; control = 3'b100;
        #10;
      if (out !== 16'hffff) begin
            $display("ERROR: XOR operation failed! Expected %h, got %h", 16'h50CD, out);
        end
        $finish;
    end
endmodule




module 16bit_ALU_tb;
    reg [15:0] in1, in2;
    reg [2:0] control;
    wire [15:0] out;
    reg [15:0] captured_out;
    reg error;

    // Instantiate DUT
    t1e3 uut (
        .in1(in1),
        .in2(in2),
        .control(control),
        .out(out)
    );

    // Task to drive input
    task automatic drive(input reg [15:0] in1, input reg [15:0] in2, input reg [2:0] control);
        begin
            // Apply inputs
            uut.in1 = in1;
            uut.in2 = in2;
            uut.control = control;
        end
    endtask

    // Task to monitor output
    task automatic monitor(output reg [15:0] captured_out);
        begin
            captured_out = uut.out;
        end
    endtask

    // Task to check output
    task automatic check(input reg [15:0] in1, input reg [15:0] in2, input reg [2:0] control, input reg [15:0] expected_out, input reg [15:0] captured_out, output reg error);
        begin
            if (captured_out !== expected_out) begin
                $display("ERROR: Control = %b, in1 = %h, in2 = %h, out = %h, Expected = %h", control, in1, in2, captured_out, expected_out);
                error = 1;
            end else begin
                $display("SUCCESS: Control = %b, in1 = %h, in2 = %h, out = %h, Expected = %h", control, in1, in2, captured_out, expected_out);
                error = 0;
            end
        end
    endtask

    // Test process
    initial begin
        error = 0;

        // ADD
        drive(16'h1234, 16'h5678, 3'b000);
        #10;
        monitor(captured_out);
        check(16'h1234, 16'h5678, 3'b000, 16'h68AC, captured_out, error);
        
        // SUB
        drive(16'h9397, 16'h8356, 3'b001);
        #10;
        monitor(captured_out);
        check(16'h9397, 16'h8356, 3'b001, 16'h1041, captured_out, error);

        // AND
        drive(16'hff00, 16'h0f0f, 3'b010);
        #10;
        monitor(captured_out);
        check(16'hff00, 16'h0f0f, 3'b010, 16'h0f00, captured_out, error);

        // OR
        drive(16'hf0f0, 16'h0f0f, 3'b011);
        #10;
        monitor(captured_out);
        check(16'hf0f0, 16'h0f0f, 3'b011, 16'hffff, captured_out, error);

        // XOR
        drive(16'hffff, 16'h0000, 3'b100);
        #10;
        monitor(captured_out);
        check(16'hffff, 16'h0000, 3'b100, 16'hffff, captured_out, error);

        $finish;
    end
endmodule

