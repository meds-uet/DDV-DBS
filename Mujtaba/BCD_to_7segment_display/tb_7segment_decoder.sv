module tb_7segment_decoder;


logic [3:0]in;
logic [6:0]binary_code;



Seven_segment_display_decoder decoder(

.in(in),
.binary_code(binary_code)

); 


initial begin

in = 4'd0;
#20
in = 4'd1;
#20
in = 4'd2;
#20
in = 4'd3;
#20
in = 4'd4;
#20
in = 4'd5;
#20
in = 4'd6;
#20
in = 4'd7;
#20
in = 4'd8;
#20
in = 4'd9;
#20;


end

   
endmodule
