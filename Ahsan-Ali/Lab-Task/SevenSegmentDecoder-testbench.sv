module SSD_testbench;

 logic [3:0] in;
 logic [6:0] out;
 
 logic [6:0] exp_out;
 
 Seven_Segemnt_Decoder DUT(.in(in), .out(out));
 
 //task to apply input
 task apply_input(input a);
   in = a;
   calculate_result;
   $display("Actual Output = %d, Expected Output = %d", out, exp_out);
    if (out === exp_out)
     $display("Test passed!");
	else
     $display("Test failed!");
 
 endtask
 //task to calculate expected output
 task calculate_result;
   case(in)     
     0: exp_out = 7'b0111111;
     1: exp_out = 7'b0000110;
     2: exp_out = 7'b1011011;
     3: exp_out = 7'b1001111;
     4: exp_out = 7'b1100110;
     5: exp_out = 7'b0101101;
     6: exp_out = 7'b1111101;
     7: exp_out = 7'b0000111;
     8: exp_out = 7'b1111111;
     9: exp_out = 7'b1101111;
	 default:
        exp_out = 7'b0111111;
	endcase 
	#10;	
 endtask
 
 initial begin 
  apply_input(0); 
  apply_input(8); 
  apply_input(2); 
  apply_input(9); 
  apply_input(4); 
  apply_input(5); 
  apply_input(1); 
  apply_input(3); 
  apply_input(7); 
  apply_input(6); 
 end
 
 endmodule
 