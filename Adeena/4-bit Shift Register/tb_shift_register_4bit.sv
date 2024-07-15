module tb_shift_register_4bit;

    logic clock;
    logic reset;
    logic serial_in;
    logic [3:0] q;

    
    shift_register_4bit uut (
        .clock(clock),
        .reset(reset),
        .serial_in(serial_in),
        .q(q)
    );

    initial begin
        clock = 0;
        forever #5 clock = ~clock; 
    end

   
    initial begin

        reset = 0;
        serial_in = 0;

        // Apply reset
        reset = 1;
        #10;
        reset = 0;

        // Apply serial input and observe the output
        serial_in = 1; #10;  // Apply 1
        serial_in = 0; #10;  // Apply 0
        serial_in = 1; #10;  // Apply 1
        serial_in = 1; #10;  // Apply 1
        serial_in = 0; #10;  // Apply 0
        serial_in = 1; #10;  // Apply 1
        serial_in = 0; #10;  // Apply 0
        serial_in = 0; #10;  // Apply 0

        // Finish simulation
        #100;
        $finish;
    end

endmodule
