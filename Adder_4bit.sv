module Adder_4bit (
input logic [3:0] a,b,
input logic cin,
output logic [3:0] sum,
output logic cout
);

// internal signals
logic c1,c2,c3;

fa fa0(.a(a[0]),.b(b[0]),.cin(cin),.sum(sum[0]),.cout(c1));
fa fa1(.a(a[1]),.b(b[1]),.cin(c1),.sum(sum[1]),.cout(c2));
fa fa2(.a(a[2]),.b(b[2]),.cin(c2),.sum(sum[2]),.cout(c3));
fa fa3(.a(a[3]),.b(b[3]),.cin(c3),.sum(sum[3]),.cout(cout));


endmodule



// Full adder 
module fa (
input logic a,b,cin,
output logic sum,cout
);

always_comb begin

sum = a^b^cin;
cout=  (a & b) | (b & cin) | (cin & a);
end

endmodule



