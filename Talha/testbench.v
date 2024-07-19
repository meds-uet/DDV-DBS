`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.07.2024 20:32:58
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
    reg [3:0] binary_input;     // 4-bit register for the binary input
    wire [6:0] segment;         // 7-bit wire for the 7-segment display output

    // Instantiate the SevenSegmentDecoder module
    SevenSegmentDecoder uut (
        .binary_input(binary_input),
        .segment(segment)
    );

    integer i;

    initial begin
        // Test all possible input combinations
        for (i = 0; i < 16; i = i + 1) begin
            binary_input = i;
            #10;
            case (binary_input)
                4'b0000: if (segment !== 7'b1111110) $display("Test failed for input 0");
                4'b0001: if (segment !== 7'b0110000) $display("Test failed for input 1");
                4'b0010: if (segment !== 7'b1101101) $display("Test failed for input 2");
                4'b0011: if (segment !== 7'b1111001) $display("Test failed for input 3");
                4'b0100: if (segment !== 7'b0110011) $display("Test failed for input 4");
                4'b0101: if (segment !== 7'b1011011) $display("Test failed for input 5");
                4'b0110: if (segment !== 7'b1011111) $display("Test failed for input 6");
                4'b0111: if (segment !== 7'b1110000) $display("Test failed for input 7");
                4'b1000: if (segment !== 7'b1111111) $display("Test failed for input 8");
                4'b1001: if (segment !== 7'b1111011) $display("Test failed for input 9");
                4'b1010: if (segment !== 7'b1110111) $display("Test failed for input A");
                4'b1011: if (segment !== 7'b0011111) $display("Test failed for input b");
                4'b1100: if (segment !== 7'b1001110) $display("Test failed for input C");
                4'b1101: if (segment !== 7'b0111101) $display("Test failed for input d");
                4'b1110: if (segment !== 7'b1001111) $display("Test failed for input E");
                4'b1111: if (segment !== 7'b1000111) $display("Test failed for input F");
                default: if (segment !== 7'b0000000) $display("Test failed for unknown input");
            endcase
        end

        $display("All test cases completed.");
        $finish;
    end
endmodule

