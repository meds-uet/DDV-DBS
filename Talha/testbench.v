`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.07.2024 20:18:38
// Design Name: 
// Module Name: testbench
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


module testbench;
    reg [15:0] a;         // 16-bit register for input a
    reg [15:0] b;         // 16-bit register for input b
    reg [2:0] control;    // 3-bit register for control signal
    wire [15:0] result;   // 16-bit wire for the output result

    // Instantiate the ALU module
    ALU16bit uut (
        .a(a),
        .b(b),
        .control(control),
        .result(result)
    );

    initial begin
        // Test Addition
        a = 16'h0001; b = 16'h0001; control = 3'b000;
        #10;
        if (result !== 16'h0002) $display("Addition test failed: %h + %h = %h", a, b, result);

        // Test Subtraction
        a = 16'h0002; b = 16'h0001; control = 3'b001;
        #10;
        if (result !== 16'h0001) $display("Subtraction test failed: %h - %h = %h", a, b, result);

        // Test AND operation
        a = 16'hFF00; b = 16'h0F0F; control = 3'b010;
        #10;
        if (result !== 16'h0F00) $display("AND test failed: %h & %h = %h", a, b, result);

        // Test OR operation
        a = 16'hFF00; b = 16'h0F0F; control = 3'b011;
        #10;
        if (result !== 16'hFF0F) $display("OR test failed: %h | %h = %h", a, b, result);

        // Test XOR operation
        a = 16'hFF00; b = 16'h0F0F; control = 3'b100;
        #10;
        if (result !== 16'hF00F) $display("XOR test failed: %h ^ %h = %h", a, b, result);

        $display("All test cases completed.");
        $finish;
    end
endmodule

