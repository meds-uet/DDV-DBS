module shift_reg(

input clk,reset,serial_in,
output  serial_out);
reg [3:0] shift_reg;

always@(posedge clk)begin
if (reset)begin
shift_reg <= 4'b0000;
end 
else
begin
shift_reg <={shift_reg [2:0],serial_in};
end
end
assign serial_out = shift_reg[3];
endmodule