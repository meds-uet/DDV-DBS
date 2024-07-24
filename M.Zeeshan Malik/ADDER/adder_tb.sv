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

     $monitor("A = %b, B = %b, sum =%b", A, B, sum);

     //Test Case 1
     A = 4'b1000; B = 4'b1111;
     #10;

     //Test Case 2
     A = 4'b1000; B = 4'b0111;
     #10;


     $stop;
  end

endmodule
     

     