`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 01:43:09 PM
// Design Name: 
// Module Name: binary_adder
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


module binary_adder( input logic [3:0] a,b,
                     output logic [4:0] c);
   int i,j; 
   int d=0; // d for carry, i for index and j to store the temporary result
    always_comb begin
    
    for (i=0 ; i<4 ; i++) begin
    j = a[i]+b[i]+d ;
    
    if (j==3) begin
    
        c[i] = 1;
        d = 1;
    
    end
    
    if (j==2) begin
        c[i]=0;
        d=1;
        end
        
    else begin
        
        c[i] = j;
        
    end
    end 
    
    
    c[4]=d; 
    
    end
    
    
    
    
endmodule
