module Seven_Segemnt_Decoder(in, out);
 input logic [3:0] in;
 output logic [6:0] out;
 
 always_comb begin
   case(in)     
     0: out = 7'b0111111; //0
     1: out = 7'b0000110; //1
     2: out = 7'b1011011; //2
     3: out = 7'b1001111; //3
     4: out = 7'b1100110; //4
     5: out = 7'b0101101; //5
     6: out = 7'b1111101; //6
     7: out = 7'b0000111; //7
     8: out = 7'b1111111; //8
     9: out = 7'b1101111; //9
	 default:
        out = 7'b0111111; //0
	endcase    
 end
 
endmodule
