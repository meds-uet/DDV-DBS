`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 01:44:01 AM
// Design Name: 
// Module Name: full_adder
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


module full_adder(input [3:0] a, b,
                  output logic [4:0] result
    );
    int d = 0;
    int carry = 0;
    
    always_comb begin
    carry = 0;
    d = 0;
    for (int i = 0; i < 4; i++)begin
    
       d = a[i] + b[i] + carry;
        if (d==3) begin
            result[i] = 1;
            carry = 1;
        end
       if (d == 2)begin
            result[i] = 0;
            carry = 1;
       end
       
       else begin
       
       result[i] = d;
       carry = 0;
       
       end
       
    end
    
     result[4] = carry;
             
    end
endmodule
