module 4bit_SR_tb ():
reg clk;
reg reset;
reg serial_in;
wire serial_out);

//instentiation
4bit_SR uut(
.clk(clk),
.reset(reset),
.serial_in(serial_in),
.serial_out(serial_out)
);
//clock generation
initial begin
clk=0;
forever #20 clk=~clk;
end
//simulation sequence

initial begin
reset=1;
serial_in=0;
#10
reset=0;
#10
serial_in=1;
#10
serial_in=0;
#10
serial_in=1;
#10
serial_in=1;

#30
$finish;
end