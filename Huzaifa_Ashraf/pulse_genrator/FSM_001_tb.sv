module FSM_001_tb;

  // Input signals
  logic clk, rst, curr;

  // Output signal
  logic d_out;

  // Instantiate the FSM design
  FSM_001 dut (.clk(clk), .rst(rst), .in(curr), .detected(d_out));

  // Reset task
  task reset();
    begin
      rst = 1'b1;
      @(posedge clk);
      rst = 1'b0;
    end
  endtask

  // Clock generation
  initial begin
    clk = 1'b0;
    forever #30 clk = ~clk;
  end

  // Initialization task
  task init_var();
    begin
      curr = 1'b0;
    end
  endtask

  // Pulse generation task
  task pulse_gen(int value);
    begin
      repeat (value) begin
        @(posedge clk);
        curr = 1'b0;
        @(posedge clk);
        curr = 1'b1;
      end
    end
  endtask

  // Automatic monitor (using always_ff for previous_val)
  always_ff @(posedge clk) begin
    if (rst) begin
      previous_val <= 1'b0;
    end else begin
      previous_val <= curr;
    end
  end

  logic previous_val = 1'b0;  // Declare previous_val outside the always_ff block

  // Automatic monitor (checking for detection signal)
  task automatic_monitor;
    begin
      forever begin
        @(posedge clk);
        if (curr === 1'b1 && previous_val === 1'b0) begin
          previous_val = curr;
          @(posedge clk);
          if (d_out !== 1'b1) begin
            $display("Error: Detected signal not asserted at expected time");
          end
        end
      end
    end
  endtask

  // Test procedure
  initial begin
    reset();
    init_var();
    fork
      pulse_gen(100);
      automatic_monitor;
    join
    $stop;
  end

endmodule
