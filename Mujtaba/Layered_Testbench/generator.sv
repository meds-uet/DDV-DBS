`include "transaction.sv"


class generator;

//transaction handle
transaction tx;

//mailbox for sending data to driver
mailbox gen2drv;


//constructor function
function new(mailbox gen2drv);
	this.gen2drv = gen2drv;
endfunction



//main task
task main();

$display("[GENERATOR] *****************GENERATOR STARTED*****************");

repeat(20) begin
	tx = new();
	tx.en_i = 1'b1;
	if(tx.randomize)
		$display("TRANSACTION RANDOMIZED");
	else $display("TRANSACTION NOT RANDOMIZED");
	gen2drv.put(tx);
end
 
$display("[GENERATOR] *****************GENERATOR ENDED*****************");




endtask




endclass
