`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/08/2024 02:52:49 PM
// Design Name: 
// Module Name: Parameterized_Counter
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: Parameterized counter with up, down, and reset controls.
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

module Parameterized_Counter #(
    parameter int WIDTH = 8 
)(
    input  logic                  clk,
    input  logic                  rst_n,
    input  logic                  up,
    input  logic                  down,
    input  logic [WIDTH-1:0]      initial_value,
    output logic [WIDTH-1:0]      count
);
    logic [WIDTH-1:0] counter;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            counter <= initial_value; 
        end else if (up && !down) begin
            if (counter < {WIDTH{1'b1}}) begin  //replication operator creates a bit-vector where each bit is set to 1. if WIDTH is 8, then {WIDTH{1'b1}} evaluates to 8'b11111111.
                counter <= counter + 1;
            end
        end else if (down && !up) begin
            if (counter > 0) begin
                counter <= counter - 1;
            end
        end
    end

    assign count = counter;

endmodule
