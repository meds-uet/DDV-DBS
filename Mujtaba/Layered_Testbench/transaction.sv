`ifndef TRANSACTION_SV
`define TRANSACTION_SV


class transaction;

rand logic [3:0]in;

logic [6:0]binary_code;


constraint data_in_constraint{
	in >= 4'b0000; 
	in <= 4'b1001;
}



function void display(string class_name);
    $display("-------------------------------------[%s]------------------------------------" , class_name);
    $display("[%0t]BCD Input = %0b                            7 sgement Binary Code = %0b",$time,in,binary_code);
    $display("----------------------------------------------------------------------------"); 
    $display("\n");
endfunction


endclass


`endif
