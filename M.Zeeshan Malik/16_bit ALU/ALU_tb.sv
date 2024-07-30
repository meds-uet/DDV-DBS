module ALU_tb;
    
     reg [15:0] A;
     reg [15:0] B;
     reg [2:0] op;
 
     logic [15:0] result;
  
     ALU uut(
      .A(A),
      .B(B),
      .op(op),
      .result(result)
);

    initial begin
 
    //Test case 1
    A = 16'h0003; B =16'h0005;op = 3'b000;
    #10;
    
 
    //Test case 2
    A = 16'h0003; B =16'h0005;op = 3'b001;
    #10;
    
    
     //Test case 3
     A = 16'h0003; B =16'h0005;op = 3'b010;
     #10;
        
        
     //Test case 4
     A = 16'h0003; B =16'h0005;op = 3'b011;
     #10;
     
     
     //Test case 5
     A = 16'h0003; B =16'h0005;op = 3'b100;
     #10;
     
     
     //Test case random
     A = 16'h0653; B =16'h0235;op = 3'b010;
     #10;
            
    $stop;

    end

endmodule