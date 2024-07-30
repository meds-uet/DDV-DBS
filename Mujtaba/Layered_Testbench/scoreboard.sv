`include "transaction.sv"

class scoreboard;

mailbox mon1_scb;
mailbox mon2_scb;


logic [15:0]in1_fifo[$];
logic [15:0]in2_fifo[$];


function new(mailbox mon1_scb, mailbox mon2_scb);
	this.mon1_scb  = mon1_scb;
    	this.mon2_scb = mon2_scb;
endfunction




task main;
	fork 
      	get_input();
      	get_output();
    	join_none;
endtask




//getting input 
task get_input();
	
transaction tx;
repeat(20) begin
	mon1_scb.get(tx);
	in1_fifo.push_back(tx.in1);
	in2_fifo.push_back(tx.in2);
	$display("Input recieved at scoreboard : in1 = %0d  ,  in2 = %0d",tx.in1,tx.in2);
end

endtask






//getting output
task get_output();

transaction tx;

logic [15:0]temp_in1,temp_in2;

forever begin
	mon2_scb.get(tx);
	$display("Ouput recieved at scoreboard(Desired Output) : Sum = %0d",tx.sum);
	temp_in1 = in1_fifo.pop_front();
	temp_in2 = in2_fifo.pop_front();
	if(temp_in1 + temp_in2 == tx.sum) begin
		$display("Ouput from refrence model , sum = %0d",temp_in1 + temp_in2);
		$display("TEST PASSED");
		$display("\n");
	end

	else begin
		$display("TEST FAILED , result not same as expected output");
		$display("\n");
	end


end


endtask





endclass
