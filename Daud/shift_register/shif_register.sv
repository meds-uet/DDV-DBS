`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/02/2024 12:23:27 PM
// Design Name: 
// Module Name: shif_register
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

module shif_register(
  input logic clk,
  input logic reset,
  input logic in,
  output logic [3:0] out
);
    reg [3:0] temp_out;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            temp_out <= 4'b0000;
        end else begin
            temp_out[0] <= in;
            temp_out[1] <= temp_out[0];
            temp_out[2] <= temp_out[1];
            temp_out[3] <= temp_out[2];
        end
    end

    assign out = temp_out;

endmodule
