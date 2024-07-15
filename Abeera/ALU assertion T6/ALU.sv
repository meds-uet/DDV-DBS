module ALU16bit (
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [2:0] sel,
    output logic [15:0] C

);

   always_comb begin
        case(sel)
            3'b000: C = A + B; //ADD
            3'b001: C = A - B; //SUB
            3'b010: C = A & B; //AND
            3'b011: C = A | B; //OR
            3'b111: C = A ^ B; //XOR
            default: C = 16'b0;
        endcase 
   end 

endmodule