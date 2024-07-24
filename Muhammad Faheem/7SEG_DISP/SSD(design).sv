module SSD(outp,inp);
input [3:0]inp;
output reg [6:0]outp;
 
always@(*)
begin
	case(inp)
	    4'h0: outp = 7'b1000000;
	    4'h1: outp = 7'b1111001;
		4'h2: outp = 7'b0100100;
		4'h3: outp = 7'b0110000;
		4'h4: outp = 7'b0011001;
		4'h5: outp = 7'b0010010;
		4'h6: outp = 7'b1000010;
		4'h7: outp = 7'b1111000;
		4'h8: outp = 7'b0000000;
		4'h9: outp = 7'b0010000;
		4'ha: outp = 7'b0001000;
		4'hb: outp = 7'b0000011;
		4'hc: outp = 7'b1000110;
		4'hd: outp = 7'b0100001;
		4'he: outp = 7'b0000110;
		4'hf: outp = 7'b0001110;
endcase
end
endmodule
