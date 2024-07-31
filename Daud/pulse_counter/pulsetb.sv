`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/09/2024 02:46:13 PM
// Design Name: 
// Module Name: pulsetb
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


module pulsetb;
logic x;
logic clk;
logic rst;
logic out;
logic reg_x;

pulse_converter uut(.clk(clk), .reset(rst), .in(x), .out(out));

initial begin
clk = 0;
forever #5 clk = ~clk;
end
// reset task
task reset();
rst = 0;
@(posedge clk)
rst = 1;
endtask

// to assign the inital value to the inputs
task int_vars;
x = 0;
reg_x = 0;
endtask
// applying pulse
task apply_pulse(int value);

repeat(value)begin 
@(posedge clk);
x <= ~x;
end
endtask

initial begin
int_vars;
reset();
fork
apply_pulse(10);
monitor();
join
$finish;
end

// monitor code

task monitor();
forever 
begin
@(posedge clk);
reg_x = x;
if(x == 1 && reg_x == 0) begin
@(posedge clk);
if(out == 0) begin
$display ("problem find");
end
end
else begin
@(posedge clk)
if(out == 1)
$display();

end
end


endtask 
endmodule
