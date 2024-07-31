/////////////////////////////////////DATA_ARRAY CODE/////////////////////////
module data_ary(
input logic clk,//comes from tb
input logic rst,//comes from tb
input logic [7:0] index_bits,
input logic [3:0] offset,
input logic [31:0] pr_write_data_in, //data_in
output logic [31:0] pr_read_data, //data_out
input logic [31:0] pr_address_tag, //processor address comes from tag array 
input logic update_write, //comes from tag_array
input logic update_read,//comes from tag_array
input logic refil_write,//comes from tag_array
input logic refil_read,//comes from tag_array
output logic [3:0][31:0] data_out_mem,//Dta_out
input logic [3:0][31:0] data_in_mem  //Data_in
);
///////////////////////////////////////////DATA MEMORY/////////////////////////////
logic [3:0][31:0] data_array [0:256];
//////////////////////////////////////////internal signals//////////////////
logic i;
/////////////////////////////////////////Assignments////////////////////////////////
//////////////////////////////////////////main functionality of this data_array//////////////
always_ff@(posedge clk) begin
if(!rst)begin
for(i=0;i<256;i=i+1)begin
data_array[i]<=256'b0;
end
data_out_mem<=0;
end
else begin
      if (update_write) begin
          data_array[index_bits][offset]<= pr_write_data_in;
          end
      if ( update_read) begin
           pr_read_data <= data_array[index_bits];
           end
   
      if (refil_read) begin
          data_array[index_bits]<=data_in_mem;
          end
       if (refil_write) begin
          data_out_mem <= data_array[index_bits];
          end
end
end
endmodule

