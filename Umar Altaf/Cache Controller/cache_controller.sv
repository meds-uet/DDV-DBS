`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/19/2024 10:59:36 AM
// Design Name: 
// Module Name: cache_controller
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module cache_controller(
input logic clk,
input rst_n,
input logic read_req,//processor read request
input logic write_req,//processor write request
input logic cache_flush,//cache flush command 
input logic [31:0] p_addr,//processor address to cache controller
output logic [31:0] m_addr,// cache controller address to memory
input logic [31:0] p_w_data,//data coming from  processor to cache controller
output logic [31:0] p_r_data,//data going from cache controller to processor
input logic [127:0]m_r_data,//data coming from memory to cahce controller
output logic [127:0]m_w_data,//data going from cache controller to memory 
input logic main_mem_ack,//memory ack when memory commplete the internal write or read operation 
output logic mem_write,// write signal enalbe when need to write the memory
output logic mem_read,// read signal enalbe when need to read the memory
output logic stall// stall from processor when cache controller intreacting with memory 
    );
 logic [127:0] cache_memory [0:255];//cache memory where data is stored 
 logic [21:0] tag_valid_dirty [0:255];//tag ,valid and dirty bits .tag [22:2],valid[1],dirty [0]
 logic [19:0] tag_p;
 logic [7:0] index_p;
 logic [3:0] offset_p;
 logic [21:0]tag_v_d;
 //logic [31:0]read_data;
 //logic [63:0]r_r_data;
 logic cache_hit;
 logic cache_miss;
 //logic cache_w_miss; 
 logic flush_done;
// logic [31:0]m_addr;
 logic flush;
 logic [7:0]i_i;
 logic [7:0]i;
 logic [19:0] tag_of_cache;
 logic [127:0]tmp_data;
 logic tmp_write_req;
 logic tmp_read_req;
 logic test;
 typedef enum logic [2:0] {IDLE,PROCESS_REQUEST,CACHE_ALLOCATE,WRITE_BACK,FLUSH} state_t;
           state_t current_state, next_state;
always_ff @(posedge clk or negedge rst_n) begin
                       if(rst_n) //reset all outputs and internal registers @ active low reset
                       begin
                       m_addr<=0;
                       p_r_data<=0;
                       m_w_data<=0;
                       mem_write<=0;
                       mem_read<=0;
                       stall<=0;
                       flush<=0;
                       i<=0;
                    
                       tag_of_cache<=20'h00000;
                       for(int j=0;j<256;j++)
                       begin
                       tag_valid_dirty[j]<=22'h000000;
                       cache_memory[j]<=128'h0000_0000_0000_0000_0000_0000_0000_0000;
                    
                       end
                       
                       current_state<=IDLE;
                       end  
                      else
                      begin  
                      current_state<=next_state; //state transition @ posedge of clk
                      end
                      end
          
           
always_ff @(posedge clk) begin 
case(current_state)
          
IDLE:
begin
cache_hit<=0;
cache_miss<=0;
tmp_read_req<=0;
tmp_write_req<=0;
stall<=0;
test<=0;
flush_done<=0;
 
if (read_req || write_req)//if read or write request from processor then distribute the addr to tag,index and offfset 
begin
 tag_p<= p_addr[31:12]; // separate the tag from address
 index_p<=p_addr[11:4];//separate the index from address
offset_p<=p_addr[3:0]; // separate the offset from address
tmp_read_req<=read_req;
tmp_write_req<=write_req;
 
next_state<=PROCESS_REQUEST;  

end
else if (cache_flush)//if cache flush then goto flush state
begin
flush<=1;//made flush one to use later 
next_state<=FLUSH;
end
else
begin
next_state<=IDLE;//if there isn't any request then stay on idle
end
end
         
PROCESS_REQUEST:
begin

if ((tag_v_d[21:2]==tag_p)&& tag_v_d[1])//seggrigate the tag from meta_data and match with tag of processor 
//also check the vaild bit
    begin
    cache_hit<=1;
        if(tmp_read_req)// if there is read hit then read data from cache
        begin
        case(offset_p)
       4'b0000:p_r_data<=cache_memory[index_p][31:0];//reading data from the cache at index on offset 00
       4'b0100:p_r_data<=cache_memory[index_p][63:32];//reading data from the cache at index on offset 01
       4'b1000:p_r_data<=cache_memory[index_p][95:64];//reading data from the cache at index on offset 10
       4'b1100:p_r_data<=cache_memory[index_p][127:96];//reading data from the cache at index on offset 11
       default:begin next_state<=IDLE;$display("the memory is word addressable.reading from wrong location");end
        endcase
        end
        else if(tmp_write_req)
        begin
          case(offset_p)
             4'b0000:cache_memory[index_p][31:0]<=p_w_data;//writting data from the processor to cache at index on offset 00
             4'b0100:cache_memory[index_p][63:32]<=p_w_data;//writting data from the processor to cache at index on offset 01
             4'b1000:cache_memory[index_p][95:64]<=p_w_data;//writting data from the processor to cache at index on offset 10
             4'b1100:cache_memory[index_p][127:96]<=p_w_data;//writting data from the processor to cache at index on offset 11
             default:begin next_state<=IDLE;$display("the memory is word addressable.writing on wrong location");end
              endcase
                tag_valid_dirty[index_p]<={tag_p,1'b1,1'b1};//when writting in cache then the dirty bit should be high
        // aslo need to add byte write and word write support later
        end
        cache_miss<=0;
       
        next_state<=IDLE;
    end
else
    begin 
        if (tag_v_d[1]==0 && tag_v_d[0]==0)//if valid bit low and dirty low then goto cache allocate and declare it miss 
        begin
        cache_miss<=1;
        stall<=1;//stall if need to goto memory
        next_state<=CACHE_ALLOCATE;
        end
        else if(tag_v_d[1] && tag_v_d[0])//if  valid bit and dirty bit is high then goto write back and declare it miss
        begin
        cache_miss<=1;
        stall<=1;//stall if need to goto memory
        tag_of_cache<=tag_v_d[21:2];// store the tag of cache so the cache date will send back to memory 
        next_state<=WRITE_BACK;
        end

    end
end
   
CACHE_ALLOCATE:
begin
if (cache_miss)
begin
mem_read<=1;
m_addr<=p_addr;
cache_memory[index_p]<=m_r_data;//memory read and stored at cache index
tag_valid_dirty[index_p]<={tag_p,1'b1,1'b0};//update the metadata array stroring the tag with valid one and dirty zero
    if (main_mem_ack)//after the write operation if memory ack then got back to process request
    begin
    stall<=0;//after memoery ack stall is removed
    mem_read<=0;
    next_state<=PROCESS_REQUEST;
    end
    else
    begin 
    next_state<=CACHE_ALLOCATE;
    end
end
end
//else if(cache_r_miss)
//begin
// case(offset_p)
//            4'b0000:cache_memory[index_p][31:0]<=p_w_data;//writting data from the processor to cache at index on offset 00
//            4'b0100:cache_memory[index_p][63:32]<=p_w_data;//writting data from the processor to cache at index on offset 01
//            4'b1000:cache_memory[index_p][95:64]<=p_w_data;//writting data from the processor to cache at index on offset 10
//            4'b1100:cache_memory[index_p][127:96]<=p_w_data;//writting data from the processor to cache at index on offset 11
//            default:begin next_state<=IDLE;$display("the memory is word addressable.writing on wrong location");end
//             endcase
//tag_valid_dirty[index_p]<={tag_p,1'b1,1'b1};
//stall<=0;
//next_state<=IDLE;
//end

WRITE_BACK:    
begin
if (cache_miss)
begin
mem_write<=1;//if cache is miss then mem need to be wrriten
m_addr<={tag_of_cache,index_p,4'b0000};//complinig adress to store in the memory location 
m_w_data<=cache_memory[index_p];//sending the data from the cache to memory as this is when dirty bit was one
//    if (main_mem_ack) //after the first write wait for memory ack
//    begin
//    mem_write<=0;
//    mem_read<=1;//again send write signal to memory to read
//    m_addr<={tag_p,index_p,4'b0000};//compile the new address where we need to take the data back to cache
//    cache_memory[index_p]<=m_r_data;//store the data to cache
//    tag_valid_dirty[index_p]<={tag_p,1'b1,1'b0};//update the meta data field and making valid bit one
//    end
end
if (flush)// if request come form the flush state 
begin
mem_write<=1;//memory signals to write 
m_addr<={tag_valid_dirty[i_i][21:2],i_i,4'b0000};//compile the addess from the index where found the dirty bit one
m_w_data<=cache_memory[i_i];// send back the data from cache to memory where dirty bit was high

end
if (main_mem_ack &&!flush)
begin
stall<=0;//after memoery ack stall is removed
mem_read<=0;
mem_write<=0;
next_state<=CACHE_ALLOCATE;
end
else if (main_mem_ack &&flush)
begin
stall<=0;//after memoery ack stall is removed
mem_write<=0;
tag_valid_dirty[i_i][1:0]<=2'b00; // @ mem ack  vaild bit of metadata is zero @ i index
next_state<=FLUSH;
end
else if(!main_mem_ack)//if memory isn't ack then stay on write back state
begin
next_state<=WRITE_BACK;
end

end    
FLUSH:    
begin
if (flush )
begin
//for (int i=0;i<3;i++)//if flush request came then iterate in the index in the cache

$display("tag dirty bit,%b and value of i %d",tag_valid_dirty[i][0],i);
    if (tag_valid_dirty[i][0]==1)//if dirty bit is high on that index
    begin
    
i_i<=i;//assign i to a register to use later
i=i+1;
stall<=1;
next_state<=WRITE_BACK;//goto write back to write to memory

    end 
   
end
else if (i==255)
//(i_i==3)
begin
flush<=0;
flush_done<=1;//showimg flush is done
next_state<=IDLE;//go  back to idle 
end



end 
endcase
end 
assign tag_v_d=tag_valid_dirty[index_p];// tag,index and offset stored in metadata reference to cache memory 
//assign p_data=read_req ?read_data:1'bz;
//assign addr=cache_miss ?m_addr:1'bz;
//assign r_data=(flush || cache_miss) ?r_r_data:1'bz;  
endmodule
