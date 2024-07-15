
module tb_Alu_16bit();

logic [15:0] a,b;
logic [15:0] y;
logic [2:0]  Alu_control;

Alu_16bit DUT(.a(a),.b(b),.Alu_control(Alu_control),.y(y) );

initial begin 
a=1;
b=1;

  for(int i=0;i<7;i++) begin   
    Alu_control=i;
    #10;
  end
end
  
endmodule