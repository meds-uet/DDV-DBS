module tb_L2P_Converter;
 logic X;
 logic clk, rstn;
 logic Y;
 bit prev_X = 0;

 
 L2P_Converter DUT(.X(X), .clk(clk), .rstn(rstn), .Y(Y));
 
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

 //task for monitor
 task automatic monitor;
  forever begin
	 @(posedge clk);
	$display("time = %0t prev_X = %b X = %b",$time, prev_X, X);	 
	  if(prev_X == 0 && X == 1) 
	   begin
		 prev_X <= X;
	     @(posedge clk);
		 $display("time = %0t prev_X = %b X = %b",$time, prev_X, X);
	   	 if(Y == 0) begin
            $display("Test Failed!");
		    $stop;
	     end
       end
	  else begin
		prev_X <= X;
	     @(posedge clk);
		 if(Y == 1) begin
		   //$display(" time = %0t prev_X = %b X = %b Y = %b",$time, prev_X, X, Y);
		   $display("Test Failed!");
		   $stop;	 	  
	    end
	  end
	  prev_X <= X;
  end
 endtask
 
 initial begin
  int_vars;
  //X = 1;
  reset;
  for (int i = 1; i < 10; i++)
      apply_pulse(i);
   $finish;  
 end
 
 initial begin
   monitor;
 end
 
endmodule

