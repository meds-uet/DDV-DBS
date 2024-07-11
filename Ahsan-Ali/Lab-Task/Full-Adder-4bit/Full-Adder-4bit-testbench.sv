module tb_fa_4bit;
//Inputs
 logic [3:0] in1, in2;
 logic carry_in;
//Outputs 
 logic [3:0] sum;
 logic carry_out;
 
 logic [3:0] exp_sum;
 bit exp_carry_out;
  
 
 fa_4bit dut(in1, in2, carry_in, sum, carry_out);
 
 task add(input logic [3:0] a,b,input logic cin);
  begin
    in1 = a;
    in2 = b;
    carry_in = cin;
	calculate_result;
     $display("Actual Sum = %d, Expected SUM = %d, Carry out = %d, Expected_Carry = %d ", sum, exp_sum, carry_out, exp_carry_out);
    if ((sum === exp_sum) && (carry_out === exp_carry_out))
     $display("Test passed!");
	else
     $display("Test failed!");
   end
 endtask
 

 task calculate_result;
   {exp_carry_out, exp_sum} = in1 + in2 + carry_in;
   #10;
 endtask
 
 initial begin
  add(0,0,0); //1
  #10
  add(1,1,1); //2
  #10
  add(1,3,0); //3
  #10
  add(2,2,1); //4
  #10
  add(3,4,0); //5
  #10
  add(5,2,1); //6
  #10
  add(7,8,0); //7
  #10
  add(9,2,1); //8
  #10
  add(2,1,0); //9
  #10
  add(8,3,1); //10
  #10
  add(13,15,0); //11
  #10
  add(14,11,1); //12
  #10
  add(15,10,1); //13
  #10
  add(5,12,1); //14
  #10
  add(14,1,0); //15
  #10
  add(15,15,1); //16
 end
 
endmodule
