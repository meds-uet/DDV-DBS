`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/09/2024 10:21:17 AM
// Design Name: 
// Module Name: TB_16_ALU
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


module TB_16_ALU();

logic [15:0] a1;
logic [15:0] b1;
logic [15:0] c1;
logic [2:0] control;

ALU DUT (.a(a1), .b(b1), .c(c1), .control(control));

// Define tasks
task perform_operation(input [15:0]a,b,
                        input [2:0]sel);
    //input logic [15:0] op_a;
    //input logic [15:0] op_b;
    //input logic [2:0] op_control;
    begin
        a1 = a;
        b1 = b;
        control = sel;
        #5;
    end
endtask

initial begin
    // Test cases using tasks
    perform_operation(16'h0000, 16'h0010, 3'b000); // Add
    perform_operation(16'h00010, 16'h0000, 3'b001); // Subtract (example operation)
    perform_operation(16'h0000, 16'h0010, 3'b010); // Another operation (example)

    $stop;
end

endmodule
