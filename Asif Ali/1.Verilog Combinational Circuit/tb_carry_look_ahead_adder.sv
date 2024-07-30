`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/29/2024 05:57:16 PM
// Design Name: 
// Module Name: tb_carry_look_ahead_adder
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
module tb_carry_look_ahead_adder;
    logic [3:0] A, B;  
    logic [3:0] Sum;  
    logic Cout;  

    carry_look_ahead_adder_4bit uut (
        .A(A),
        .B(B),
        .Sum(Sum),
        .Cout(Cout)
    );

    task driver(input logic [3:0] a_in, input logic [3:0] b_in);
        begin
            A = a_in;
            B = b_in;
            #10;  
        end
    endtask

     task monitor();
        begin
            $display("Time=%0t : A=%b, B=%b, Sum=%b, Cout=%b", $time, A, B, Sum, Cout);
        end
    endtask

     initial begin
        $display("Starting test sequence...");
        $monitor("%0d: A=%b, B=%b => Sum=%b, Cout=%b", $time, A, B, Sum, Cout);

         driver(4'b0000, 4'b0000); monitor();
        driver(4'b0001, 4'b0001); monitor();
        driver(4'b0010, 4'b0011); monitor();
        driver(4'b0100, 4'b0101); monitor();
        driver(4'b0110, 4'b0010); monitor();
        driver(4'b0111, 4'b1000); monitor();
        driver(4'b1000, 4'b0111); monitor();
        driver(4'b1001, 4'b0001); monitor();
        driver(4'b1010, 4'b0100); monitor();
        driver(4'b1100, 4'b0100); monitor();
        driver(4'b1011, 4'b0011); monitor();
        driver(4'b1101, 4'b0011); monitor();
        driver(4'b1110, 4'b0001); monitor();
        driver(4'b1111, 4'b0000); monitor();
        driver(4'b1111, 4'b1111); monitor();
        driver(4'b1100, 4'b1100); monitor();

        $display("Test sequence completed.");
        $stop; // Stop simulation
    end

endmodule

