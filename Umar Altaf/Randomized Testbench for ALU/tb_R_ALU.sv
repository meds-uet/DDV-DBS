`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/04/2024 02:26:32 PM
// Design Name: 
// Module Name: tb_R_ALU
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


module tb_R_ALU;
  logic [15:0]in1;
logic [15:0]in2;
logic [2:0] operation;
logic clk;
logic [16:0]out;
logic [16:0]result1;

R_ALU ALU1(in1,in2,operation,out);
initial begin 
   clk = 0;
  forever 
     #5 clk = ~clk;
end
//initial
//begin
//$monitor("in1 = %b,in2 = %b,opeartion =%b,out = %b,result1 = %b", in1,in2,operation, out, result1);
// end
initial
begin



//@(posedge clk); 
//@(posedge clk);  


//in1=$urandom();
//in2=$urandom();
//operation=$urandom();

//@(posedge clk); 
//@(posedge clk);  
//result1=result(in1,in2,operation);  
//@(posedge clk);  
//@(posedge clk);  
//@(posedge clk);
//@(posedge clk);  
//@(posedge clk);
//@(posedge clk);  
//@(posedge clk);
//assert(result1 ==out) else $display("Test failed: in1=%b, in2=%b, operation=%b, result1=%b, out=%b", in1, in2, operation, result1, out);
//@(posedge clk);  
//in1=$urandom();
//in2=$urandom();
//operation=$urandom();
////@(posedge clk); 
////@(posedge clk);  
//result1=result(in1,in2,operation); 
////@(posedge clk);  
//@(posedge clk);  
//@(posedge clk);
//@(posedge clk);  
//@(posedge clk);
//@(posedge clk);  
//@(posedge clk);
//assert(result1 ==out) else $display("Test failed: in1=%b, in2=%b, operation=%b, result1=%b, out=%b", in1, in2, operation, result1, out); 
 
for (integer i=0;i<10;i++)
begin

    in1=$urandom();
    in2=$urandom();
    operation=$urandom();
 
    result1=result(in1,in2,operation);  
   @(posedge clk);
    assert(result1 ==out) else $display("Test failed: in1=%b, in2=%b, operation=%b, result1=%b, out=%b", in1, in2, operation, result1, out);

    $display("in1 = %b,in2 = %b,opeartion =%b,out = %b,result1 = %b", in1,in2,operation, out, result1);
     

end

repeat(20) @(posedge clk);


 
$finish;

end
function automatic [16:0] result;
//reg [16:0]out1;
input [15:0]in1,in2;
input [2:0] opreration;

    begin
     if (operation==0)
    begin
    result=in1+in2;
    end
   else  if (operation==1)
              begin
              result=in1-in2;
              end
    else  if (operation==2)
                     begin
                     result=in1&in2;
                     end
 else  if (operation==3)
                            begin
                            result=in1|in2;
                            end
    else  if (operation==4)
                                   begin
                                   result=in1^in2;
                                   end
                                   else
                                   result=0;

    
    end
//    assign out=out1;
endfunction

endmodule
