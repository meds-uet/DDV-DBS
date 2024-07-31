`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/04/2024 01:10:34 PM
// Design Name: 
// Module Name: tb_p_fifo
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


module tb_p_fifo;

 

  logic reset;

logic rd,we,clk;
logic [7:0]data;
logic [7:0] dataout;
// 
//reg increment,decrement;
//dmux4 m4(dataout,addr[0],addr[1],m[0],m[1],m[2],m[3]);
//initial 
//begin
//dataout=1;
//addr=2;
//#10
//dataout=1;
//addr=1;
//#10
//dataout=1;
//addr=0;
//#10
//dataout=1;
//addr=3;


  p_fifo f1 (reset,clk,rd,we,data,dataout);


//count c1(reset,clk,increment,decrement,counts);
integer f;
 initial begin 
   clk = 0;
  forever 
     #5 clk = ~clk;
end

 
//initial
//begin
//f = $fopen("fifof.xt","w");
//$fmonitor(f,"data = %d,dataout = %d", data, dataout);
// end
initial
begin
//reset =1;
//#5
//reset=0;
//#5
//increment=0;
//decrement=1;
//#5
//increment=0;
//decrement=1;
//#5
//increment=0;
//decrement=1;
//#5
//increment=0;
//decrement=1;
//#5
//increment=0;
//decrement=1;
reset=1;
we=0;
rd=0;

#9 
reset=0;

@(posedge clk);
data=5;
we=1;
rd=0;
@(posedge clk);

data=10;
we=1;
rd=0;


@(posedge clk);

data=20;

we=1;
rd=0;

@(posedge clk);

data=30;

we=1;
rd=0;

@(posedge clk);

data=40;

we=1;
rd=0;
@(posedge clk);

data=50;

we=1;
rd=0;
@(posedge clk);

data=60;

we=1;
rd=0;
@(posedge clk);

data=70;

we=1;
rd=0;
@(posedge clk);

data=80;

we=1;
rd=0;
@(posedge clk);

rd=0;
@(posedge clk);

rd=1;
@(posedge clk);

rd=0;
@(posedge clk);

rd=1;
@(posedge clk);

rd=0;
@(posedge clk);

rd = 1;
@(posedge clk);

data=90;

we=1;
rd=0;
@(posedge clk);

we=0;
rd = 1;
@(posedge clk);

//
//#9;
//data=$random;
//we=$random;
//cs=1;
//addr=$random;
//rd=$random;
//
//@(posedge clk);
//@(posedge clk);
//@(posedge clk);
//data=$random;
//we=$random;
//cs=1;
//addr=$random;
//rd=$random;
//
//@(posedge clk);
//@(posedge clk);
//@(posedge clk);
//data=$random;
//we=$random;
//cs=1;
//addr=$random;
//rd=$random;
//
//@(posedge clk);
//@(posedge clk);
//@(posedge clk);
//data=$random;
//we=$random;
//cs=1;
//addr=$random;
//rd=$random;
//
//@(posedge clk);
//@(posedge clk);
//@(posedge clk);
//data=$random;
//we=$random;
//cs=0;
//addr=$random;
//rd=$random;

repeat(20) @(posedge clk);


 

end
//    initial begin
//    $dumpfile("dump.vcd"); $dumpvars;
//    #300;
//    $finish();
//  end
endmodule


