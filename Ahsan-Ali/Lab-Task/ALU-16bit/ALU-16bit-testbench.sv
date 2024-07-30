module tb_alu_16bit;
 //Inputs
 logic [15:0] A, B;
 logic [2:0] Sel;
 //Output
 logic [15:0] Y;
 //expected output
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
	
 task apply_input(input logic [15:0] in1, in2, input logic [2:0] sel);	
  begin
   A = in1;   
   B = in2;
   Sel = sel;
   compute_expected_output;
    $display("Actual Output = %d, Expected Output = %d", Y, exp_out);
    if (Y === exp_out)
     $display("Test passed!");
	else
     $display("Test failed!");  
  end
 endtask
 
 initial begin
   apply_input(12,23,3'b000);              
   apply_input(112,100,3'b001);              
   apply_input(16'b0001101001110111, 16'b0001101001110111, 3'b010);              
   apply_input(16'b1001101001110111, 16'b10001101001110101, 3'b011);              
   apply_input(16'b1101110011011001, 16'b1110111011010001, 3'b100);              
   apply_input(420, 300, 3'b000);              
   apply_input(8001, 6000, 3'b100);              
   apply_input(16'b0101101011010011, 16'b1010111001100101, 3'b010);              
 end

endmodule
