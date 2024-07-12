`include "transaction.sv"

class scoreboard;

mailbox mon2scb;



function new(mailbox mon2scb);
	this.mon2scb = mon2scb;
endfunction



task main();
	transaction tx;
        repeat (20) begin
            mon2scb.get(tx);
	    tx.display("SCOREBOARD CLASS");

	    case(tx.in)
	    4'b0000:begin tx.binary_code = 7'b1111110;$display("TEST PASSED");end//abcdefg        
    	    4'b0001:begin tx.binary_code = 7'b0110000;$display("TEST PASSED");end      
	    4'b0010:begin tx.binary_code = 7'b1101101;$display("TEST PASSED");end
            4'b0011:begin tx.binary_code = 7'b1111001;$display("TEST PASSED");end
            4'b0100:begin tx.binary_code = 7'b0110011;$display("TEST PASSED");end
            4'b0101:begin tx.binary_code = 7'b1011011;$display("TEST PASSED");end
            4'b0110:begin tx.binary_code = 7'b1011111;$display("TEST PASSED");end
            4'b0111:begin tx.binary_code = 7'b1110000;$display("TEST PASSED");end
            4'b1000:begin tx.binary_code = 7'b1111111;$display("TEST PASSED");end
            4'b1001:begin tx.binary_code = 7'b1111011; $display("TEST PASSED");end 

	    default:$display("TEST FAILED");
	    endcase
	    
	
        
        end
endtask



endclass
