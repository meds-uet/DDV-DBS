module pulse_generator_tb;

    // Parameters
    localparam CLK_PERIOD = 10;  // Clock period in ns (100 MHz clock)

    // Testbench signals
    logic clk;            // Clock signal
    logic reset_n;        // Active-low reset signal
    logic signal_in;      // Input signal to the pulse generator
    logic pulse_out;     // Output pulse from the pulse generator
    logic previous_signal; // To track previous value of signal_in

    // Instantiate the Unit Under Test (UUT)
    pulse_generator uut (
        .clk(clk),
        .reset_n(reset_n),
        .signal_in(signal_in),
        .pulse_out(pulse_out)
    );

    // Clock generation
    initial begin
        clk = 1'b0;
        // Clock toggles every 5 ns (half of the CLK_PERIOD)
        forever #(CLK_PERIOD / 2) clk = ~clk;  
    end

    // Track previous value of signal_in
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            // On reset, clear previous_signal
            previous_signal <= 1'b0;
        end else begin
            // Update previous_signal on each clock edge
            previous_signal <= signal_in;
        end
    end

    // Test stimulus
    initial begin
        // Initialize signals
        reset_n = 1'b0;     // Apply reset to initialize the UUT
        signal_in = 1'b0;   // Set input to 0
        #(CLK_PERIOD * 2);  // Wait for 2 clock cycles to ensure reset propagation

        // Release reset
        reset_n = 1'b1;     
        #(CLK_PERIOD * 2);  // Wait for 2 clock cycles to allow normal operation

        // Test Case 1: Rising edge detection
        signal_in = 1'b1;   // Set input to 1 (rising edge detected)
        #(CLK_PERIOD);      // Wait for one clock cycle
        signal_in = 1'b0;   // Set input back to 0
        #(CLK_PERIOD * 2);  // Wait for 2 clock cycles
        // Expect pulse_out to be high for one clock cycle

        // Test Case 2: No pulse generation if input stays high
        signal_in = 1'b1;   // Set input to 1
        #(CLK_PERIOD * 3);  // Wait for 3 clock cycles
        signal_in = 1'b0;   // Set input back to 0
        #(CLK_PERIOD * 2);  // Wait for 2 clock cycles
        // Expect pulse_out to be 0 throughout this period

        // Test Case 3: Multiple rising edges
        signal_in = 1'b1;   // Set input to 1
        #(CLK_PERIOD);      // Wait for one clock cycle
        signal_in = 1'b0;   // Set input to 0
        #(CLK_PERIOD);      // Wait for one clock cycle
        signal_in = 1'b1;   // Set input to 1 again
        #(CLK_PERIOD);      // Wait for one clock cycle
        signal_in = 1'b0;   // Set input back to 0
        #(CLK_PERIOD * 2);  // Wait for 2 clock cycles
        // Expect pulse_out to generate a pulse for each rising edge

        // End simulation
        #(CLK_PERIOD * 20); // Wait for 20 clock cycles before finishing
        $finish;
    end

    // Monitor to display signals
    initial begin
        // Display signal values at each time step
        $monitor("Time: %0t | clk: %b | reset_n: %b | signal_in: %b | pulse_out: %b",
                 $time, clk, reset_n, signal_in, pulse_out);
    end

    // Check for pulse generation correctness
    assert property (@(posedge clk) disable iff (!reset_n)
        (signal_in == 1 && !previous_signal) |-> ##1 (pulse_out == 1))
    else $error("Pulse generation failed: rising edge detection issue.");

endmodule
