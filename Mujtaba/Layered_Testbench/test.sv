`include "environment.sv"

program test(design_interface _if);
  environment env;
  
  initial begin
    env = new(_if);
    
    env.run_test();
  end
endprogram
