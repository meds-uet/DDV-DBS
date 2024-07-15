
module tb_Decoder_7seg();

logic [3:0] bcd;
logic [6:0] seg;

Decoder_7seg  DUT(.bcd(bcd),.seg(seg));


initial begin

for ( int i=0;i<16;i++)
    begin
	bcd=i;
	#10;
	end
    
end


endmodule