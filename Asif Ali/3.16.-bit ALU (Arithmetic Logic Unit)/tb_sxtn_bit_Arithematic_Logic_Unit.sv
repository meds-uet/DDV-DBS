`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/29/2024 06:25:31 PM
// Design Name: 
// Module Name: tb_sxtn_bit_Arithematic_Logic_Unit
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

module tb_Sxteeen_bit_Arithematic_Logic_Unit;
    reg [15:0] A, B;
    reg [2:0] control;
    wire [15:0] result;

    Sixtn_bit_Arithematic_Logic_Unit uut (
        .A(A),
        .B(B),
        .control(control),
        .result(result)
    );

    initial begin
        // Monitor the signals
        $monitor("A = %h, B = %h, control = %b, result = %h", A, B, control, result);

        // Test Addition
        A = 16'h1234; B = 16'h5678; control = 3'b000;
        #10;
        A = 16'hFFFF; B = 16'h0001; control = 3'b000;
        #10;

        // Test Subtraction
        A = 16'h5678; B = 16'h1234; control = 3'b001;
        #10;
        A = 16'h0001; B = 16'h0001; control = 3'b001;
        #10;

        // Test AND
        A = 16'hF0F0; B = 16'h0F0F; control = 3'b010;
        #10;
        A = 16'hAAAA; B = 16'h5555; control = 3'b010;
        #10;

        // Test OR
        A = 16'hF0F0; B = 16'h0F0F; control = 3'b011;
        #10;
        A = 16'hAAAA; B = 16'h5555; control = 3'b011;
        #10;

        // Test XOR
        A = 16'hF0F0; B = 16'h0F0F; control = 3'b100;
        #10;
        A = 16'hAAAA; B = 16'h5555; control = 3'b100;
        #10;

        // Finish simulation
        $finish;
    end
endmodule

