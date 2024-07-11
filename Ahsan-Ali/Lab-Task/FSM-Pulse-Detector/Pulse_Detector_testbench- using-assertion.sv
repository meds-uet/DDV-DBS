module Pulse_Detector_testbench;
 logic X;
 logic clk, rstn;
 logic Y;
 bit prev_X = 0;

 
 Pulse_Detector DUT(.X(X), .clk(clk), .rstn(rstn), .Y(Y));
 
 initial begin
  clk = 0;
  forever #10 clk = ~clk;
 end
 
 //reset task
 task reset;
   begin
       rstn = 0;
     @(posedge clk)
       rstn = 1; 
   end
 endtask
 //to assign the initial value to inputs
 task int_vars;
  begin
   X = 0;
  end
 endtask
 //applying pulse
 task apply_pulse(int value);
  begin
   @(posedge clk);      
   X <= 1;
   repeat(value) @(posedge clk);
   X <= 0;
  end
 endtask

   property check_pulse;
      @(posedge clk) (!X ##1 X) |-> ##1 Y;   
   endproperty

 assert property (check_pulse) 
  $display("Assertion passed at the time = %0t", $time);
 else 
   $display("Assertion failed at time = %0t;", $time);


 initial begin
  int_vars;
  //X = 1;
  reset;
  for (int i = 1; i < 10; i++)
      apply_pulse(i);
   $finish;  
 end
 
endmodule
