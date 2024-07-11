//For a common cathode type 7 segment display

module Seven_segment_display_decoder(

input [3:0]in,

output logic [6:0]binary_code

);



always_comb begin

case(in)
    
    4'b0000:
        binary_code = 7'b1111110;//abcdefg        
    4'b0001:
        binary_code = 7'b0110000;        
    4'b0010:
        binary_code = 7'b1101101;
    4'b0011:
        binary_code = 7'b1111001;
    4'b0100:
        binary_code = 7'b0110011;
    4'b0101:
        binary_code = 7'b1011011;
    4'b0110:
        binary_code = 7'b1011111;
    4'b0111:
        binary_code = 7'b1110000;
    4'b1000:
        binary_code = 7'b1111111;
    4'b1001:
        binary_code = 7'b1111011;     
  
endcase


end



endmodule
