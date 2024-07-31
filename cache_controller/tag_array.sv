
///////////////////////////////////TAG ARRRAY CODE/////////////////////////////////////
//data array module
module tag_ary(
input logic clk, //comes from tb
input logic rst,//comes from tb
input logic read_in,//comes from processor
input logic [7:0] index_bits,
input logic [19:0] tag_bits,
input logic write_in,//comes from processor 
input logic read_ack,//comes from data_arry
input logic write_ack, //comes from data_arry
output logic update_write,cache_hit,cache_miss,
output logic update_read,
output logic refil_write,
output logic refil_read 
  
);
//////////////////////////////////Signals in data_array used fo instentiation in tag array//////////////
/*
logic update_write;
logic update_read;
logic refil_write;
logic refil_read;
*/
///////////////////////////////////TAG ARRAY MEMORY   & valid & dirty///////////////////////////////////
logic [19:0] tag_array[0:255];
logic  valid_bit [255:0];
logic dirty_bit [255:0];
/////////////////////////////////////INTERNAL SIGNALS//////////////////////////////////////////////////////////
//logic valid_bit,dirty_bit;
//logic cache_hit;
//logic cache_miss;
//logic i;
/*
assign update_write = write_in & cache_hit;
assign update_read  = read_in & cache_hit;
assign refil_write  = write_ack && cache_miss;
assign refil_read   = read_ack && cache_miss;
*/
///////////////////////////////////////////////////STATES DEFINATIONS//////////////////////////////////////////////////
typedef enum logic [2:0] {IDLE,PROCESS_REQUEST,WRITE_BACK,CACHE_ALLOCATE,FLUSH}state_t;
state_t current_state,next_state;
///////////////////////////////////////////////ASSIGNMENTS////////////////////////////////////////////////////////
//assign tag_bits   = pr_address_data_ary[31:12];
//assign index_bits = pr_address_data_ary[11:4];
//assign valid_bit  = cache_line[index_bits][149];
//assign dirty_bit  = cache_line[index_bits][148]; 

///////////////////////////////////////////RESET STATES CONDITION/////////////////////////////////////////
always_ff@(posedge clk)begin
if(!rst)begin
   current_state<=IDLE;
   end
else begin
     current_state<=next_state;
     end
end


////////////////////////////////////////STATES INER FUNCTIONALITY////////////////////////////////
always_comb begin
if(!rst)begin
for(int i=0;i<256;i=i+1)
tag_array[i]=0;
for(int i=0;i<256;i=i+1)begin
valid_bit[i]=0;
dirty_bit[i]=0;
end
cache_hit=0;
cache_miss=0;
update_write=0;
update_read=0;
refil_write=0;
refil_read=0;
end
else begin
assign update_write = write_in & cache_hit;
assign update_read  = read_in & cache_hit;
assign refil_read   = read_ack && cache_miss;
//assign refil_write  = write_ack && cache_miss;
if(current_state==IDLE)begin
end


else begin
 if(current_state==PROCESS_REQUEST)begin
     if ((tag_array[index_bits]== tag_bits) && valid_bit[index_bits]==1)begin
           cache_hit=1;
           cache_miss=0;
         if(update_write)begin
                  valid_bit[index_bits]=1;
                  dirty_bit[index_bits]=1;
             
         end 
      else if (update_read ) begin  
       end
       end
else  begin
cache_miss=1;

end
end
else if(current_state==CACHE_ALLOCATE)begin
       //cache_miss=1;
       //refil_write=0;
       if(refil_read)begin
             valid_bit[index_bits]=1;
          end
          
            //HERE IF READ_ACK ARRIVES THEN DATA ARRAY READS DATA FROM TESTBENCH(MAIN MEMORY)
   
//end
else if(current_state==WRITE_BACK)begin
       //cache_miss=1;
       //refil_read=0;
       if(refil_write)begin
                valid_bit[index_bits]=1;
                dirty_bit[index_bits]=0;
          end
   end         //HERE IF WRITE_ACK ARRIVES THEN DATA ARRAY WRITES DATA TO  TESTBENCH(MAIN MEMORY)
end
end

end
end
//////////////////////////////////////////////////STATES TRANSITION///////////////////////////////////////

always_comb begin
next_state=current_state;
//next_state=current_state;
case(current_state)
      IDLE : begin
           if(read_in | write_in)begin
              next_state = PROCESS_REQUEST;
           end
   else begin
      next_state = IDLE;
   end
end
PROCESS_REQUEST : begin
if (cache_hit && dirty_bit[index_bits]==0)begin
     next_state=IDLE;                                                                                     
    end
          else if(dirty_bit[index_bits]==0 && cache_miss)  begin
                next_state=CACHE_ALLOCATE;  
          end 
          
          else if (dirty_bit[index_bits] ==1 && cache_miss )begin
               next_state= WRITE_BACK;
          end
else begin
next_state=PROCESS_REQUEST;
end
end
CACHE_ALLOCATE : begin
if(read_ack && cache_miss)begin
    next_state=PROCESS_REQUEST;
    end 
else if (!read_ack) begin
    next_state= CACHE_ALLOCATE;
    end
end
WRITE_BACK : begin
if(write_ack && cache_miss)begin
   next_state=CACHE_ALLOCATE;
   end 
else if (!write_ack) begin
   next_state=WRITE_BACK;
   end
end
endcase
end  

endmodule
