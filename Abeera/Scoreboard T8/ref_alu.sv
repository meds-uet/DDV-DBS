module ALU_ref(
      input logic [7:0] A,
      input logic [7:0] B, 
      input logic [2:0] op,
      output logic [7:0] result_expected
);

 always_comb begin
     case(op)
       3'b000 : result_expected = A + B;
       3'b001 : result_expected = A - B;
       3'b010 : result_expected = A & B;
       3'b011 : result_expected = A | B;
       3'b100 : result_expected = A * B;
       default: result_expected = 7'b0;
     endcase
end 
endmodule