
`include "interface.sv"
`include "environment.sv"

module testbench;

    add_if aif();
 

  pulse_conv uut ( 
    .clk(aif.clk),
    .reset(aif.reset),
    .X(aif.X),
    .det(aif.det)
    );

  initial begin
    aif.clk = 0;
  end
  
  always #5 aif.clk = ~aif.clk;
  
  task rst;
    begin
      aif.reset = 1;
      #20
      aif.reset = 0;
    end
  endtask
    
  environment env;
    
  initial begin
    env = new(aif);
    rst();
    env.run();
    $finish();
  end

   
    initial begin
        $dumpfile("dump.vcd"); 
        $dumpvars;
    end

endmodule