`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/10/2024 02:32:33 PM
// Design Name: 
// Module Name: alu_tb
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


module alu_tb;
    parameter WIDTH = 16;
    
    // Signals for ALU inputs and output
    logic [WIDTH-1:0] a1, b1, c1;
    logic [2:0] sel1;
    
    // Clock period parameter
    localparam period = 10;
    
    // Instantiate the ALU module
    alu DUT (.a(a1), .b(b1), .sel(sel1), .c(c1));
    
    // Task to apply inputs to the ALU
    task apply_inp(
        input logic [WIDTH-1:0] x, 
        input logic [WIDTH-1:0] y, 
        input logic [2:0] selection
    );
    begin
        a1 = x;
        b1 = y;
        sel1 = selection;
        #period;
    end
    endtask
    
    // Initial block to apply test vectors
    initial begin
        apply_inp(16'h5, 16'h10, 3'b000); // Test addition
        apply_inp(16'h5, 16'h10, 3'b001); // Test subtraction
        apply_inp(16'h5, 16'h10, 3'b010); // Test bitwise AND
        apply_inp(16'h5, 16'h10, 3'b011); // Test bitwise OR
        apply_inp(16'h5, 16'h10, 3'b100); // Test bitwise XOR
        $stop; // Stop the simulation
    end    
endmodule
