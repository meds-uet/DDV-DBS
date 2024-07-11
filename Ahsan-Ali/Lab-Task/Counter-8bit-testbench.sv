module tb_counter_8bit;
 
 parameter WIDTH = 8;
 //Inputs
 logic [WIDTH-1:0] in;
 logic clk, rstn, up, down;
 //Outputs
 logic [WIDTH-1:0] count;
 
 logic [WIDTH-1:0] exp_count;
 
 counter_8bit dut(.initial_value(in),
                  .clk(clk),
				  .rstn(rstn),
				  .up(up),
				  .down(down),
				  .count(count)
                 );  
 
 initial begin
  clk = 0;
  forever #5 clk = ~clk; 
 end
 
 task apply_input(input logic down_cnt, up_cnt, input logic [7:0] initial_value);
   in <= initial_value;
   up <= up_cnt;
   down <= down_cnt;
 endtask
 
 initial begin
  @(posedge clk) rstn <= 0;
  apply_input(0, 0, 63);
  #10;
  rstn <= 1;
  apply_input(1, 0,0);
  #100;
  rstn <= 0;
  apply_input(0, 0, 100);
  #100;
  rstn <= 1;
  apply_input(0, 1, 0);
  #100;
 $finish;
 end
 
endmodule;
