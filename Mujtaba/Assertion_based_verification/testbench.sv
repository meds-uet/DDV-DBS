class transaction;

rand logic X_i;

function void display(input logic X_i , Y_o);
	$display("Input = %0b        Y_o = %0b",X_i,Y_o);
endfunction


endclass





module testbench;


logic clk_i;
logic reset_i;
logic X_i;

logic Y_o;



transaction tx;





state_machine FSM(

.clk_i(clk_i),
.reset_i(reset_i),
.X_i(X_i),
.Y_o(Y_o)

);



//------ASSERTION BASED VERIFICATION------

property level_pulse_converter_check;
	@(posedge clk_i) disable iff (reset_i) X_i |=> ##1 (Y_o ##1 !Y_o)
endproperty



initial begin

	assert property(level_pulse_converter_check)
		$error("Pulse is not generated at output");
end


//------------------------------------------



initial begin
	tx = new();


repeat(100) begin
	assert(tx.randomize()) begin
		$display("RANDOMIZATION SUCCESSFULL");
	end

	else $error("RANDOMIZATION FAILED");
	@(posedge clk_i);
	X_i = tx.X_i;

	#20;

	tx.display(X_i , Y_o);
end

end





initial begin
	clk_i = 0;
	forever #20 clk_i = ~clk_i;
end



initial begin
	reset_i = 1;
	#60
	reset_i = 0;
end





endmodule
