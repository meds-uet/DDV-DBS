module tb_LP_Converter;
 logic a;
 logic clk, rstn;
 logic b;
 bit prev_a = 0;

 
 L2P_Converter DUT(.a(A), .clk(clk), .rstn(rstn), .b(B));
 
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

 task int_vars;
  begin
   a = 0;
  end
 endtask
 
 task apply_pulse(int value);
  begin
   @(posedge clk);      
   a <= 1;
   repeat(value) @(posedge clk);
   a <= 0;
  end
 endtask


 task automatic monitor;
  forever begin
	 @(posedge clk);
	$display("time = %0t prev_a = %b a = %b",$time, prev_a, a);	 
	  if(prev_a == 0 && a == 1) 
	   begin
		 prev_a <= a;
	     @(posedge clk);
		 $display("time = %0t prev_a = %b a = %b",$time, prev_a, a);
	   	 if(Y == 0) begin
            $display("Test Failed!");
		    $stop;
	     end
       end
	  else begin
		prev_X <= X;
	     @(posedge clk);
		 if(Y == 1) begin
		   //$display(" time = %0t prev_a = %b a = %b b = %b",$time, prev_a, a, b);
		   $display("Test Failed!");
		   $stop;	 	  
	    end
	  end
	  prev_a <= a;
  end
 endtask
 
 initial begin
  int_vars;
  //X = 1;
  reset;
  for (int i = 1; i < 10; i++)
      apply_pulse(i);
   $stop;  
 end
 
 initial begin
   monitor;
 end
 
endmodule

