`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/11/2024 08:50:22 AM
// Design Name: 
// Module Name: Counter
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

module Counter#(parameter WIDTH = 3)(
    input logic clk,               // Clock signal
    input logic reset,             // Reset signal
    input logic enable,            // Enable signal
    input logic count_up,          // Count up/down control signal
    input logic [WIDTH-1:0] init_value,  // Initial value
    output logic [WIDTH-1:0] d     // Output value
);

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        d <= init_value;           // Initialize d to init_value on reset
    end else if (enable) begin
        if (count_up) begin
            d <= d + 1;            // Increment d if count_up is high
        end else begin
            d <= d - 1;            // Decrement d if count_up is low
        end
    end
end

endmodule
