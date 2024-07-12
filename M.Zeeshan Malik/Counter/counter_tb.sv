module counter_tb;
      
      localparam WIDTH=8;
      
      logic clk;
      logic reset;
      logic up;
      logic down;
      logic enable;
      logic [WIDTH-1:0] init_value;
      logic[WIDTH-1:0] counter;
      
      counter #(
         .WIDTH(WIDTH)
)  uut(
        
        .clk(clk),
        .reset(reset),
        .up(up),
        .down(down),
        .init_value(init_value),
        .enable(enable),
        .counter(counter)
);

   initial begin
        clk=0;
        up = 0;
        down = 0;
        enable = 0;
        init_value = 0;
        forever #5 clk= ~clk;
      end
   
    initial begin
       reset = 1;
       #10;
       reset = 0;
       #10;
 
       enable = 1;
       #10;
       init_value = 6;
       #10;
       enable = 0;
       #10;
       //init_value = 180;
       //#10;

    end
     
   //always #10 up = ~up;
    always #10 down = 1;
    //always #50 enable = ~enable;
    initial #100 $finish;


endmodule
       
        
      
