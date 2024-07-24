module fa_1bit(a,b,c_in,sum,c_out);

 input logic a;
 input logic b;
 input logic c_in;
 output logic sum;
 output logic c_out;

 assign {c_out,sum} = a+b+c_in;

endmodule

module fa_4bit(a,b,c_in,s,c_out);
 parameter WIDTH=4;
 input logic [WIDTH-1:0] a,b;
 input logic c_in;
 output logic [WIDTH-1:0] s;
 output logic c_out;
 logic [WIDTH-1:0] temp;

fa_1bit fa1 (.a(a[0]), .b(b[0]), .c_in(c_in), .sum(s[0]), .c_out(temp[0]));
fa_1bit fa2 (.a(a[1]), .b(b[1]), .c_in(temp[0]), .sum(s[1]), .c_out(temp[1]));
fa_1bit fa3 (.a(a[2]), .b(b[2]), .c_in(temp[1]), .sum(s[2]), .c_out(temp[2]));
fa_1bit fa4 (.a(a[3]), .b(b[3]), .c_in(temp[2]), .sum(s[3]), .c_out(c_out));


endmodule
