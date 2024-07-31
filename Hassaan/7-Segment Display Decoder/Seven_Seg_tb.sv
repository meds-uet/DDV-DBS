`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/10/2024 01:08:57 PM
// Design Name: 
// Module Name: Seven_Seg_tb
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

module Seven_Seg_tb;

// Testbench signals
logic [3:0] x1;
logic [6:0] y1;
localparam period = 10; // Define clock period

// Instantiate the Device Under Test (DUT)
Seven_Seg DUT (
    .x(x1),
    .y(y1)
);

initial begin
    // Apply test vectors with a delay of 'period' between each
    integer i;
    for (i = 0; i < 16; i++) begin
        x1 = i;
        #period;
    end

    // Stop simulation
    $stop;
end

endmodule
