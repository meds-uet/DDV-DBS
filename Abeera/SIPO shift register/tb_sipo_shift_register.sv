
module tb_sipo_shift_register;

    // Inputs
    logic clk;
    logic reset;
    logic serial_in;

    // Outputs
    logic [3:0] parallel_out;

    sipo_shift_register uut (
        .clk(clk), 
        .reset(reset), 
        .serial_in(serial_in), 
        .parallel_out(parallel_out)
    );

    initial begin
        // Initialize Inputs
        clk = 0;
        reset = 1;
        serial_in = 0;
        #10;
        reset = 0;

        // Apply test stimulus
        serial_in = 1; #10;
        serial_in = 0; #10;
        serial_in = 1; #10;
        serial_in = 1; #10;

        // Wait for a while
        #50;

        // End simulation
        $stop;
    end

    // Clock generation
    always #5 clk = ~clk;

endmodule