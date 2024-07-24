module SSD_tb;
    // Declare variables for input and output
    logic [3:0] inp;
    logic [6:0] outp;
    
    // Instantiate the SSD module
    SSD uut (
        .inp(inp),
        .outp(outp)
    );

    // Task to apply input
    task apply_input(input [3:0] value);
        begin
            inp = value;
            #10; // Wait for 10 time units for output to settle
        end
    endtask

    // Task to check the output
    task check_output(input [6:0] expected);
        begin
            if (outp !== expected) begin
                $display("Error: input = %h, output = %b, expected = %b", inp, outp, expected);
            end else begin
                $display("Success: input = %h, output = %b", inp, outp);
            end
        end
    endtask

    // Initial block to apply the test cases
    initial begin
        // Apply and check all possible input values
        apply_input(4'h0); check_output(7'b1000000);
        apply_input(4'h1); check_output(7'b1111001);
        apply_input(4'h2); check_output(7'b0100100);
        apply_input(4'h3); check_output(7'b0110000);
        apply_input(4'h4); check_output(7'b0011001);
        apply_input(4'h5); check_output(7'b0010010);
        apply_input(4'h6); check_output(7'b1000010);
        apply_input(4'h7); check_output(7'b1111000);
        apply_input(4'h8); check_output(7'b0000000);
        apply_input(4'h9); check_output(7'b0010000);
        apply_input(4'ha); check_output(7'b0001000);
        apply_input(4'hb); check_output(7'b0000011);
        apply_input(4'hc); check_output(7'b1000110);
        apply_input(4'hd); check_output(7'b0100001);
        apply_input(4'he); check_output(7'b0000110);
        apply_input(4'hf); check_output(7'b0001110);

        $stop; // Stop simulation
    end
  initial begin
     // Open dump file for waveform analysis
        $dumpfile("SSD_tb.vcd");
        $dumpvars(0, SSD_tb);
  end
endmodule