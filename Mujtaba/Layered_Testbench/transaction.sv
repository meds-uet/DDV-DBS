`ifndef TRANSACTION_SV
`define TRANSACTION_SV


class transaction;

logic en_i;

rand logic [15:0]in1;
rand logic [15:0]in2;

logic [15:0]sum;



constraint  adder_c {

in1 >= 16'd0;
in1 <= 16'd100;

in2 >= 16'd0;
in2 <= 16'd100;

}



function void print();
	$display("***********************Transaction**********************");
	$display("in1 = %0d      in2 = %0d     enable = %0d      sum = %0d",in1,in2,en_i,sum);
	$display("********************************************************");

endfunction 






endclass

`endif
