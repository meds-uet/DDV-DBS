module alu_tb();
reg [15:0] a;
reg [15:0] b;
reg [2:0] sel;
reg [15:0] out;

//instentiation
alu_design uut(
.a(a),
.b(b),
.sel(sel),
.out(out)
);
initial begin
a=16'b1;
b=16'b0;
sel=3'b100;
#10;
end
endmodule
