////////////////////////////////////////////TOP FILE///////////////////
module tope_module (

//data_array_signals
input clk,
input  rst,
input [31:0] address,
input  [31:0] pr_write_data_in,//data_in 
output  [31:0] pr_read_data, //data_out
output logic [3:0][31:0] data_out_mem,//Data_out
input logic [3:0][31:0] data_in_mem,//Data_in


//tag_array_signals
input  read_in,
input  write_in,
input  read_ack,   
input  write_ack

);
//data_array  signals
logic update_w; 
logic update_r;
logic [31:0] pr_address_tag;
logic refil_r;
logic refil_w;


//tag_array signals
logic update_write;
logic update_read;
logic refil_write;
logic refil_read;
//logic [31:0]pr_address_data_ary;


logic [3:0]offset;
logic[19:0]tag_bits;
logic [7:0]index_bits;


assign offset[3:0]=address[3:0];
assign index_bits[7:0] = address[11:4];
assign tag_bits[19:0]= address[31:12];





//tag_array instentiation
tag_ary uuv(
.read_ack(read_ack),
.write_ack(write_ack),
.clk(clk),
.rst(rst),
.tag_bits(tag_bits),
.index_bits(index_bits),
.read_in(read_in),
.write_in(write_in),
//.pr_write_data(pr_write_data_in),
//.pr_address_data_ary(pr_addre),
.update_write(update_write),
.update_read(update_read),
.refil_read(refil_read),
.refil_write(refil_write)
);

//instentiation
data_ary uue (
.clk(clk),
.rst(rst),
.pr_read_data(pr_read_data),
.pr_write_data_in(pr_write_data_in),
.data_out_mem(data_out_mem),
.data_in_mem(data_in_mem),
.update_write(update_write),
.update_read(update_read),
.refil_read(refil_read),
.refil_write(refil_write),
.index_bits(index_bits),
.offset(offset)
);

endmodule