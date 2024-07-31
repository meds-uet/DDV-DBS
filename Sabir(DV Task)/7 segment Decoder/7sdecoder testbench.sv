module SevenSegmentDecoder_tb;

    // Testbench signals
    logic [3:0] binary_in;
    logic [6:0] segments;
    
    // Instantiate the 7-segment display decoder
    SevenSegmentDecoder uut (
        .binary_in(binary_in),
        .segments(segments)
    );

    // Task to display the output
    task display_output;
        input [3:0] bin;
        input [6:0] seg;
        begin
          $display("Input 4 bit: %b, Output segment: %b", bin, seg);
        end
    endtask

    initial begin
        // Test all possible inputs
        for (int i = 0; i < 16; i++) begin
            binary_in = i;
            #10;
            display_output(binary_in, segments);
        end
        
        // Finish simulation
        $finish;
    end

endmodule
