module ALU_16bit(Y,A,B,C);

	input [15:0]A, B;
	input [2:0]C;
	output reg [15:0]Y;

	always@(*)
	case(C)
		3'd0: Y=A+B;
		3'd1: Y=A-B;
		3'd2: Y=A&B;
		3'd3: Y=A|B;
		3'd4: Y=A^B;
		default: Y= 16'd0;
	endcase

endmodule