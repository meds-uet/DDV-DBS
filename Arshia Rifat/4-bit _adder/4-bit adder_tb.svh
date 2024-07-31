module t1e1_tb();
  logic[3:0] a;
  logic [3:0]b;
  wire [4:0]sum;
  t1e1 uut(.a(a), .b(b), .sum(sum));
  integer i, j;
  reg[4:0]sum2;
initial begin
  for (i=7; i<11; i++) begin
      for (j=0; j<7; j++) begin
         a = i;
         b= j;
         sum2 = a+b;
         #20
        if (sum !== sum2) 
           begin
             $display("ERROR: A = %b, B = %b, Sum = %b, Expected = %b", a, b,sum,     sum2);
           end 
        else 
          begin
            $display("A = %b, B = %b, Sum = %b, Expected = %b", a, b,sum, sum2);
          end
       end
   end
   $finish;
end
endmodule

