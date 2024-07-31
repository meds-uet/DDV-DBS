`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/08/2024 10:37:36 PM
// Design Name: 
// Module Name: level_pulse_tb
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

module tb_level_to_pulse;

  // Inputs
  reg clk;
  reg reset;
  reg x;

  // Outputs
  wire [1:0] out_pulse;

  // Instantiate the Unit Under Test (UUT)
  level_to_pulse uut (
    .clk(clk),
    .reset(reset),
    .x(x),
    .out_pulse(out_pulse)
  );

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk; // 10ns period clock
  end

  // Task to apply inputs
  task apply_input;
    input logic reset_in;
    input logic x_in;
    input int cycles;
    begin
      reset = reset_in;
      x = x_in;
      repeat(cycles) @(posedge clk);
    end
  endtask

  // Task to check outputs
  task check_out;
    input logic [1:0] exp_res;
    begin
      if (out_pulse != exp_res) begin
        $display("ERROR: Expected %b, got %b at time %0t", exp_res, out_pulse, $time);
      end else begin
        $display("Test passed: Expected %b, got %b at time %0t", exp_res, out_pulse, $time);
      end
    end
  endtask

  // Task to monitor input x
  task monitor;
    logic x_pre;
    begin
      x_pre = x;
        $display("INFO: x_pre = %b at time %0t", x, $time);
      forever begin
        @(posedge clk);
        if (reset) begin
          x_pre = 0;
          $display("INFO: Reset is active at time %0t", $time);
        end else begin
          $display("INFO: x = %b at time %0t", x, $time); // Display value of x after posedge
          if (x_pre != x) begin
            $display("ERROR: x changed from %b to %b at time %0t", x_pre, x, $time);
            check_out(out_pulse); // Call check_out to compare the output as well
          end
          $display("ERROR: x not changed from %b to %b at time %0t", x_pre, x, $time);
          //x_pre = x;
        end
      end
    end
  endtask

  // Initial block for testing
  initial begin
    // Apply reset
    apply_input(1, 0, 1); // Apply reset
    #10;
    check_out(2'b00);
    #10;
    apply_input(0, 1, 1); // Release reset
    #10;
    check_out(2'b00);
    #10;

    // Start monitoring
    ///fork
      //monitor();
    //join_none

    // Additional test cases
    apply_input(0, 0, 10);
    check_out(2'b01);

    apply_input(0, 1, 1);
    check_out(2'b10);

    // Additional test cases can be added here
    // ...

    $stop;
  end

endmodule





