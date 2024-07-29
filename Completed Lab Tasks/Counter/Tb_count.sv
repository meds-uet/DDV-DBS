`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/11/2024 02:13:22 PM
// Design Name: 
// Module Name: Tb_count
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

`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/11/2024 02:13:22 PM
// Design Name: 
// Module Name: Tb_count
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

module Tb_count#(parameter w=4);

    logic [w-1:0] a1;
    logic sel, reset, clk;
    logic [w-1:0] b1;

  
    Count DUT (.a(a1), .b(b1), .clk(clk), .reset(reset), .sel(sel));

   
    initial begin
        clk = 0;
        forever #3 clk = ~clk;
    end

  
    initial begin
        
        a1 = 4'b0000;
        sel = 1;
        reset = 1;
        #5 reset = 0;

        
        #20 sel = 0;  
        #20 sel = 1;  

      
        #50 $finish;
    end

endmodule
