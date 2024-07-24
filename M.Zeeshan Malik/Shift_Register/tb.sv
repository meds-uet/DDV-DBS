module shift_regtb;
      
     reg clk;
     reg reset;
     reg serial;

     logic [3:0]shift_reg;

     shift_reg uut(
     
      .clk(clk),
      .reset(reset),
      .serial(serial),
      .serial_out(serial_out)
);

      initial begin
        clk=0;
        forever #5 clk= ~clk;
      end
      
      initial begin
       
          reset = 1;
          serial =0;
          #10
          reset = 0;
          

      end
     
      always #10 serial = ~serial;
      initial #100 $finish;
      
endmodule