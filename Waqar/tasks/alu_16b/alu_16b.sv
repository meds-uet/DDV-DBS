module alu_16b(input logic [15:0] a_i,b_i,
               input logic [2:0] alu_ctrl_i,
               output logic [16:0] c_o);
    
    always @* begin
        case(alu_ctrl_i)
            3'b000: c_o = a_i + b_i;
            3'b001: c_o = a_i - b_i;
            3'b010: c_o = a_i & b_i;
            3'b011: c_o = a_i | b_i;
            3'b100: c_o = a_i ^ b_i; 
            default: c_o = a_i + b_i;
        endcase
    end

endmodule