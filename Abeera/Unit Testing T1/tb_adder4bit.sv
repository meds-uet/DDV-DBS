module tb_adder4bit;
logic [3:0] a;
logic [3:0] b;
logic [4:0] adderout;

adder_4bit uut(
    .a(a),
    .b(b),
    .adderout(adderout)
);

int i,j;

initial begin
    // 16test cases for this module and using i and j for 16 test cases
    for (i=0; i < 16; i= i +1) begin
        for (j =0; j <16; j = j +1) begin
            a = i;
            b = j;
            #10 // 10 units wait to display out
            $display("The sum of %b and %b is %b at time %0t", a, b, adderout, $time);
        end
    end
end

endmodule


