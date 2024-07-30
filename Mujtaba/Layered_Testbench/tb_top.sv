module tb_top;

logic clk;
logic reset;



design_interface _if(clk , reset);


test TEST(_if);



sequential_adder DUT(

clk,
reset,
_if.en_i,
_if.in1,
_if.in2,
_if.sum

);






initial begin
	clock_gen(20);
end


initial begin
	reset_seq(50);
end






//*************TASKS****************

task clock_gen(int time_units);
	clk = 0;
	forever #time_units clk = ~clk; 
endtask



task reset_seq(int reset_time);
	reset = 1;
	#reset_time
	reset = 0;
endtask


//***********************************








endmodule
