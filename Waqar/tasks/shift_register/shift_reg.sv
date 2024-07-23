module shift_reg_4b(input logic clk_i, rst_i,
                    input logic d_i,
                    output logic q_o);

        logic [3:0] shift_reg;
        int i;
        
        always_ff @(posedge clk_i) begin
            if(~rst_i) begin
                shift_reg <= 4'b0000;
            end
            else begin
                shift_reg [3] <= shift_reg [2];
                shift_reg [2] <= shift_reg [1];
                shift_reg [1] <= shift_reg [0];
                shift_reg [0] <= d_i;
            end
        end

            

        assign q_o = shift_reg[3];
        
endmodule