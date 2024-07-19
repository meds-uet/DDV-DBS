`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.07.2024 20:46:14
// Design Name: 
// Module Name: paramCounter #
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


module paramCounter #(
    parameter WIDTH = 8  // Parameter to specify the width of the counter
)(
    input wire clk,           // Clock signal
    input wire rst,           // Reset signal
    input wire up,            // Up control signal
    input wire down,          // Down control signal
    input wire [WIDTH-1:0] initial_value, // Initial value input
    output reg [WIDTH-1:0] count  // Counter output
);

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            count <= initial_value;  // Reset the counter to the initial value
        end else begin
            if (up) begin
                count <= count + 1;  // Increment the counter
            end else if (down) begin
                count <= count - 1;  // Decrement the counter
            end
        end
    end

endmodule

