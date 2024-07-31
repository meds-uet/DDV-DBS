module Cache_Controller(

      input logic clk,
	  input logic rst,
	  input logic read,
	  input logic write,
	  input logic c_flush,
	  input logic [31:0] pr_addr,
	  input logic [31:0] pr_data,
	  output logic [31:0] data_out,
      output logic mem_write_req,	  
      output logic [31:0] mem_addr,         
      input logic [127:0] mem_read_data,
	  output  logic mem_read_req,
      output logic [127:0] mem_write_data,
      input logic Ready_signal
);

     logic [19:0] p_tag;
	 logic [7:0] p_index;
	 logic [3:0] p_offset;
	 logic cache_miss;
	 logic cache_hit;
	 logic mem_read_ack;
	 logic mem_write_ack;
	 logic [19:0]test ;
	 logic temp_write;
	 logic temp_read;
	 
	  
	logic [149:0] cache [0 : 255];  
	
	logic [19:0] cache_tag = cache[p_index][149:130];
    logic cache_valid = cache[p_index][129];
	logic cache_dirty = cache[p_index][128];
	logic [127 :0] cache_data = cache[p_index][127:0];
	 
	typedef enum logic [2:0] {IDLE, PROCESS_REQ, CACHE_ALLOCATE, FLUSH, WRITE_BACK} state_t;
    state_t current_state, next_state;
	 
	always_ff @(posedge clk or posedge rst) begin
	    if (rst)begin
		   current_state <= IDLE;
		end else begin
		   current_state <= next_state;
		end
	end
	
	always_ff  @(posedge clk or posedge rst) begin
	    if(rst) begin
		   data_out <= 32'b0;
		   cache_dirty <= 1'b0;
		   cache_valid <= 1'b0;
		   mem_read_req <= 1'b0;
           mem_write_req <= 1'b0;
		   temp_read <= 1'b0;
		   temp_write <= 1'b0;
		end else begin
		   case (current_state)
                IDLE: begin
					if (read || write) begin
                        next_state <= PROCESS_REQ;
						cache_valid <= 0;
						cache_hit <= 1'b0;
                        p_tag <= pr_addr[31:12];
                        p_index <= pr_addr[11:4];
                        p_offset <= pr_addr[3:0];
						temp_read <= read;
						temp_write<= write;
                    end else if (c_flush) begin
                        next_state <= FLUSH;
                    end else begin
                        next_state <= IDLE;
                    end
                end
				
			    PROCESS_REQ: begin
			        cache_hit <= 1'b0;
					mem_read_req <= 1'b0;
                    if (cache_tag == p_tag && cache_valid) begin
                        cache_hit <= 1'b1;
						
                        if (temp_read) begin
							case(p_offset)
						     4'b0000:data_out <= cache_data[31:0] ;
							 4'b0100:data_out <= cache_data[63:32] ;
						     4'b1000:data_out<= cache_data[95:64];
						     4'b1100:data_out <= cache_data[127:96];
							 //default:begin next_state<= IDLE; 
							 //end
						   endcase
						   next_state <= IDLE;
                        end else if (temp_write) begin 
						   case(p_offset)
						     4'b0000:cache_data[31:0] <= pr_data;
							 4'b0100:cache_data[63:32] <= pr_data;
						     4'b1000:cache_data[95:64] <= pr_data;
						     4'b1100:cache_data[127:96] <= pr_data;
							default:begin next_state<= IDLE;							
							end
							endcase
                            //cache[p_index][127:0] <= cache_data;
                            cache_valid <= 1'b1; 
                            cache_dirty <= 1'b1; 
                            cache_tag <= p_tag;
                       
                            next_state <= IDLE;
						end
                      end else begin
                        cache_miss <= 1'b1;
						cache_tag <= p_tag;
						cache_dirty <= cache[p_index][128]; 
						if(!cache_dirty)begin
                           next_state <= CACHE_ALLOCATE;
						end else if (cache_dirty) begin
						   next_state <= WRITE_BACK;
						  mem_write_req <= 1'b1;
						   mem_write_data <= cache_data;
						end
                    end
			     end
			   
				
			    WRITE_BACK:begin
				   mem_write_req <= 1'b1;
				   mem_addr <= {cache_tag, p_index, 4'b0};  
                   if (Ready_signal && cache_miss) begin
                       mem_write_req <= 1'b0;
                       next_state <= CACHE_ALLOCATE;
					   mem_write_ack <= 1'b1;
				   end else begin
				       mem_write_ack <= 1'b0;
					   mem_write_req <= 1'b1;
					   next_state <= WRITE_BACK;
                   end
                end
				
				CACHE_ALLOCATE: begin
                   mem_addr <= pr_addr;
				   mem_read_req <= 1'b1;
				   if( Ready_signal && cache_miss) begin
				   cache_tag <= p_tag;  
                   cache_valid <= 1'b1;       
                   cache_dirty <= 1'b0;       
                   cache_data <= mem_read_data;
				   cache_miss <= 0;
				   mem_read_ack <= 1'b1;
				   end
                   if (mem_read_ack && mem_read_req) begin
                        mem_read_req <= 1'b0;
						mem_read_ack <= 1'b1;
					    next_state <= PROCESS_REQ;
						end
				   if(!mem_read_ack && mem_read_req) begin
				        mem_read_ack <= 1'b0;
						mem_read_req <= 1'b1;
						next_state <= CACHE_ALLOCATE;
                   end
                end
              endcase
            end
			cache[p_index][127:0] = cache_data;
            cache[p_index][149:130] = cache_tag;
            cache[p_index][129] = cache_valid ;
	        cache[p_index][128] = cache_dirty;
          end
endmodule