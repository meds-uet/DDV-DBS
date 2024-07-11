module tb_alu_16bit;
 //Inputs
 logic [15:0] A, B;
 logic [2:0] Sel;
 //Output
 logic [15:0] Y;
 //expected Output
 logic [15:0] exp_out;
 
 alu_16bit dut(.in1(A), .in2(B), .sel(Sel), .out(Y));
 
 task compute_expected_output;
        begin
            case(Sel)
                3'b000: exp_out = A + B;  // ADD
                3'b001: exp_out = A - B;  // SUB
                3'b010: exp_out = A & B;  // AND
                3'b011: exp_out = A | B;  // OR
                3'b100: exp_out = A ^ B;  // XOR
                default: exp_out = 16'd0;
            endcase
        end
		#10;
 endtask
 
 task apply_input;
    A = $urandom;
    B = $urandom;
    Sel = $urandom % 5; // Generate random values between 0 and 4 for sel
	compute_expected_output;
	$display("Actual Output = %d, Expected Output = %d", Y, exp_out);
     if (Y === exp_out)
        $display("Test passed!");
	 else
        $display("Test failed!");  
 endtask
 
 initial begin
	apply_input;    
	apply_input;    
	apply_input;    
	apply_input;    
	apply_input;    
	apply_input;    
	apply_input;    
	apply_input;    
	apply_input;    
	apply_input;    
 end		

endmodule
