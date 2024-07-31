`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/04/2024 09:27:19 AM
// Design Name: 
// Module Name: tb_p_counter
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


module tb_p_counter;

   
  reg reset;

reg up,down,clk,set;
reg [7:0]count,set_value;



  p_counter cp (reset,clk,up,down,set,set_value,count);


//count c1(reset,clk,increment,decrement,counts);
integer f;
 initial begin 
   clk = 0;
  forever 
     #5 clk = ~clk;
end

 
initial
begin
f = $fopen("fifof.xt","w");
$fmonitor(f,"count = %d",count);
 end
initial
begin

reset=1;

#9 
reset=0;

@(posedge clk);
set=1;
set_value=8;
@(posedge clk);
set=0;

up=1;


@(posedge clk);

up=1;



@(posedge clk);
up=0;
down=1;

@(posedge clk);


repeat(20) @(posedge clk);


 

end
    initial begin
    $dumpfile("dump.vcd"); $dumpvars;
    #300;
    $finish();
  end

endmodule
