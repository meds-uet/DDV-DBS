`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/24/2024 09:07:42 PM
// Design Name: 
// Module Name: paramtereized_counter
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


module parameterized_counter #(
    parameter WIDTH = 8  // Width of the counter
) (
    input logic clk,        // Clock signal
    input logic rst_n,      // Active-low reset
    input logic up,         // Count up control
    input logic down,       // Count down control
    input logic [WIDTH-1:0] init_val, // Initial value
    output logic [WIDTH-1:0] count    // Counter output
);

    // Register to hold the counter value
    reg [WIDTH-1:0] count_reg;

    // Counter logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            count_reg <= init_val; // Reset to initial value
        end else if (up && !down) begin
            count_reg <= count_reg + 1; // Increment
        end else if (!up && down) begin
            count_reg <= count_reg - 1; // Decrement
        end
    end

    // Output assignment
    assign count = count_reg;

endmodule

