module ALU(
      input logic [15:0] A,
      input logic [15:0] B, 
      input logic [2:0] op,
      output logic [15:0] result
);

 always_comb begin
     case(op)
       3'b000 : result = A + B;
       3'b001 : result = A - B;
       3'b010 : result = A & B;
       3'b011 : result = A | B;
       3'b100 : result = A ^ B;
       default: result = 16'b0;
     endcase
end 
endmodule