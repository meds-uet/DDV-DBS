`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 02:57:01 PM
// Design Name: 
// Module Name: ALU_16bits_tb
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

module ALU_16bits_tb;

    // Inputs and outputs
    bit [15:0] inp1;
    bit [15:0] inp2;
    bit [2:0] sel;
    bit [15:0] out;

    // Instantiate the DUT (Design Under Test)
    ALU_16bits dut (
        .inp1(inp1),
        .inp2(inp2),
        .sel(sel),
        .out(out)
    );

    // Initial block for stimulus generation
    initial begin
        // Reset values
        inp1 = 16'h0000;
        inp2 = 16'h0000;
        sel = 3'b000;

        // Print initial values
        $display("Initial values: inp1 = %h, inp2 = %h, sel = %b, out = %h", inp1, inp2, sel, out);

        // Test cases
        repeat (10) begin
            // Randomize inputs
            inp1 = $random;
            inp2 = $random;
            sel = $urandom_range(0, 7); // Randomize sel between 0 and 7

            // Apply inputs to DUT
            #5; // Wait for propagation

            // Display current inputs and output
            $display("Test case %0d: inp1 = %h, inp2 = %h, sel = %b, out = %h", 
                      $time, inp1, inp2, sel, out);
        end

        // Finish simulation after test cases
        #10;
        $finish;
    end
endmodule
