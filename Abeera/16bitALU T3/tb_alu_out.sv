module tb_alu_out;
logic [15:0] a;
logic [15:0] b;
logic [2:0] sig;
logic [15:0] out;
logic[15:0] expected_result;
int i, f, l;

Alu_16bit uut(
    .a(a),
    .b(b),
    .sig(sig),
    .out(out)
);

initial begin
    for (f = 0; f < 2; f = f +1) begin
        for (l = 0; l < 2; l = l +1) begin
            a = f;
            b = l;
            for(i = 0; i < 8; i = i +1) begin
                sig = i;
                case(sig)
                3'b001: expected_result = a + b; //1
                3'b010: expected_result = a -b; //2
                3'b011: expected_result = a & b; //3
                3'b100: expected_result = a | b; //4
                3'b101: expected_result = a ^ b; //5
                default: expected_result = 16'b0; //handle cases like 000,111,110
                endcase
                #10
                $display("For input %b, output is %b, expected output is %b", sig, out, expected_result);

                if (out != expected_result) begin
                    $display("Mismatch found as output is %b, but expected output is %b", out, expected_result);
                end else begin
                    $display(" Matched result as output is %b = expected is %b", out, expected_result);
                end
            end
        end
    end
    $finish;  
end
endmodule