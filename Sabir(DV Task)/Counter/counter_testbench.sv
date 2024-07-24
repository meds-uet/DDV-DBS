module top();
  reg clk = 1'b0;
  reg rst = 1'b0;
  reg count_up_down = 1'b1; // Initialize the counter to up running
  wire [1:0] count_val;
  
  up_down_counter #(2) count(
 .clk (clk),
 .rst(rst),                           .count_up_down(count_up_down),
.count_val(count_val));
  
  // Generate clk
  always
    #5 clk = ~clk;
    
  // Generate Stimulus
   initial begin
     #10 rst = 1'b1;
     #30 count_up_down = 1'b0;
     #50 count_up_down = 1'b1;
     #100 $finish();
   end
  
    initial begin
    $dumpfile("dump.vcd");
    $dumpvars();
  end
  
endmodule
