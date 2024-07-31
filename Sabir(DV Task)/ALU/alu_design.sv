module ALU_16bit (
    input  logic [15:0] A, B,
    input  logic [2:0]  f_Sel,
    output logic [15:0] Out
);
    always_comb begin
      case (f_Sel)
            3'b000: Out = A + B;        // Add
            3'b001: Out = A - B;        // Subtrct
            3'b010: Out = A & B;        // AND
            3'b011: Out = A | B;        // OR
            3'b100: Out = A ^ B;        // XOR
           default: Out = 16'h0000;    // Default case
        endcase
    end
endmodule
