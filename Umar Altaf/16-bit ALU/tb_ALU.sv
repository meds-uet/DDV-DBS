`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2024 02:40:20 PM
// Design Name: 
// Module Name: tb_ALU
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


module tb_ALU;
   logic [15:0]in1;
logic [15:0]in2;
logic [2:0] operation;
logic clk;
logic [16:0]out;
logic [16:0]result;
ALU ALU1(in1,in2,operation,out);
initial begin 
   clk = 0;
  forever 
     #5 clk = ~clk;
end
initial
begin
$monitor("in1 = %b,in2 = %b,opeartion =%b,out = %b,result = %b", in1,in2,operation, out, result);
 end
initial
begin



@(posedge clk); 
@(posedge clk);  


in1=$urandom();
in2=$urandom();
operation=$urandom();

//@(posedge clk); 
//@(posedge clk);  
task1(in1,in2,operation,result);  
@(posedge clk);  
@(posedge clk);  
@(posedge clk);
@(posedge clk);  
@(posedge clk);
@(posedge clk);  
@(posedge clk);
if (result!=out)
begin
$display( "The result case 1 is incorrect");
end
@(posedge clk);  
in1=$urandom();
in2=$urandom();
operation=$urandom();
//@(posedge clk); 
//@(posedge clk);  
task1(in1,in2,operation,result);  
//@(posedge clk);  
@(posedge clk);  
@(posedge clk);
@(posedge clk);  
@(posedge clk);
@(posedge clk);  
@(posedge clk);
if (result!=out)
begin
$display( "The result case 2 is incorrect");
end
@(posedge clk);  
 
in1=$urandom();
in2=$urandom();
operation=$urandom();
@(posedge clk); 
@(posedge clk);  
task1(in1,in2,operation,result);  
@(posedge clk);  
@(posedge clk);
@(posedge clk);  
@(posedge clk);
@(posedge clk);  
@(posedge clk);
if (result!=out)
begin
$display( "The result case 3 is incorrect");
end  

repeat(20) @(posedge clk);


 
$finish;

end
task task1(input [15:0]in1,input [15:0]in2,input [2:0] opreration,output reg [16:0]out );
//reg [16:0]out1;

    begin
     if (operation==0)
    begin
    out=in1+in2;
    end
   else  if (operation==1)
              begin
              out=in1-in2;
              end
    else  if (operation==2)
                     begin
                     out=in1&in2;
                     end
 else  if (operation==3)
                            begin
                            out=in1|in2;
                            end
    else  if (operation==4)
                                   begin
                                   out=in1^in2;
                                   end
                                   else
                                   out=0;

    
    end
//    assign out=out1;
endtask

endmodule
