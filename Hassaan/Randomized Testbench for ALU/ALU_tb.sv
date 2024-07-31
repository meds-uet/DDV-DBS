`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/17/2024 05:06:33 PM
// Design Name: 
// Module Name: ALU_tb
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

module ALU_tb;

parameter WIDTH = 16;
logic [WIDTH-1:0] a1, b1, c1;
logic [2:0] sel1;

// Instantiate the Device Under Test (DUT)
ALU #(WIDTH) DUT (
    .a(a1),
    .b(b1),
    .sel(sel1),
    .c(c1)
);

// Function to compute expected output
function logic [WIDTH-1:0] expected_output(
    logic [WIDTH-1:0] x,
    logic [WIDTH-1:0] y,
    logic [2:0] selection
);
    logic [WIDTH-1:0] result;

    case(selection)
        3'b000 : result = x + y;
        3'b001 : result = x - y;
        3'b010 : result = x & y;
        3'b011 : result = x | y;
        3'b100 : result = x ^ y;
        default : result = 16'bx;
    endcase

    return result;
endfunction

// Testbench initial block
initial begin
    integer i;
    logic [WIDTH-1:0] result;

    for (i = 0; i < 10; i++) begin
        a1 = $random;
        b1 = $random;
        sel1 = $random % 5;
        result = expected_output(a1, b1, sel1);
        #10;

        // Assert to check if actual output matches expected output
        assert (c1 == result) else
            $fatal("Mismatch: a1=%h, b1=%h, sel1=%h, result=%h, c1=%h", a1, b1, sel1, result, c1);
    end

    $stop;
end

endmodule
