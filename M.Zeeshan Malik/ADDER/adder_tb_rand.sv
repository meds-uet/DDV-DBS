module adder_tb;

     reg [3:0] A;
     reg [3:0] B;

     logic [4:0]sum;

     adder uut(
      
        .A(A),
        .B(B),
        .sum(sum)
);

     initial begin

     integer i;
    // $random;

     for ( i = 0; i < 16 ; i = i + 1) begin
             
         A = $random % 16;
         B = $random % 16;
         #10;
      end
     
     $stop;
end

endmodule
     

     