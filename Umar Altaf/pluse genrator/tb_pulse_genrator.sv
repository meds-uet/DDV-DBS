`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/08/2024 11:29:13 AM
// Design Name: 
// Module Name: tb_pulse_genrator
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


module tb_pulse_genrator;
logic clk;
logic x;
logic y;
logic reset;
pulse_genrator pg(clk,reset,x,y);
initial begin 
   clk = 0;
  forever 
     #5 clk = ~clk;
end

initial 
begin
reset1();
//monitor();
end

initial 
begin
//reset1();
@(posedge clk);
monitor();

end


initial begin 

for (int i=1;i<5;i++)
begin
variables(i);
//monitor();

//assert property (@(posedge clk) disable iff (!reset)
//    (x==0 |=> x==1 |=>y==1))else $display ("result is incorrect");
end

      
   repeat(5) @(posedge clk);
   $finish; 
end

task reset1();
begin

reset<=1;
@(posedge clk)
reset<=0;
end
endtask
task variables(int v);
begin
x=0;
repeat (v) @ (posedge clk)
x=1;

end
endtask
 task monitor();

 logic prev_x;
 logic current_x;
 logic prev_y;
 logic current_y;

  forever
 
 begin
 
 prev_x=x;
 $display("prev_x=%b at time=%t",x,$time);
 @(posedge clk)
 if(prev_x==0&&x==1)
 begin
  prev_x=x; 
   $display("prev_x=%b at time=%t",x,$time);
 @(posedge clk)
 if(y==0) $error("output is incorrect");
 else if (y==1) $display ("output is correct");
 end
 else $display("no transition from 0 to 1");
 
 
// current_x=x;
// $display("next_x=%b and prev_y= %b  at time=%t",x,y,$time);
// @(posedge clk)
// prev_y=y;
// @(posedge clk)
// current_y=y;
//$display("next_y=%b at time=%t",y,$time);
// if(perv_x==0 && current_x==1)
// begin
// if(prev_y==1 && current_y==0)
// $display("the pluse is genrated ");
// else 
//  $display("the output is incorrect "); 
//end
//else 
//$display("There is no transition from 0 to 1 in input"); 
 
// end
 end
 
 endtask



endmodule
