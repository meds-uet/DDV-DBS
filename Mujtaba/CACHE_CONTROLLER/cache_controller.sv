import cache_defs::*;

module cache_controller#(parameter DATA_WIDTH = 32,
			 parameter CACHE_LINES = 4096)(

input logic clk,
input logic reset,

input logic flush,
input logic [DATA_WIDTH-1:0]address,
input logic [DATA_WIDTH-1:0]data_in,//data from memory to cache
input logic main_mem_ack,

//defined in cache defs
input CPU_Request_type cpu_request,

output logic hit,
output logic miss,



output logic [128-1:0]data_out,//data from cache to memory
output logic read_done,
output logic write_done,

output logic busy





);





//defined in cache_defs
Address_type address_fields;





//states of cache controller
typedef enum logic [2:0]{

IDLE,
PROCESS_REQUEST,
CACHE_ALLOCATE,
WRITE_BACK,
FLUSH

}cache_states;


//state definition
cache_states current_state , next_state;



//extracting from address
always_comb begin

address_fields.tag = address[31:12];
address_fields.index = address[11:4];
address_fields.offset = address[3:0];

end




//internal signals
logic flush_done;







//logic for state transition
always_ff @(posedge clk) begin

if(reset) begin
  current_state <= IDLE;
end

else begin
   current_state <= next_state;
end

end


logic i = 0;






//logic for next state
always_ff @(posedge clk) begin
    if (reset) begin
        hit <= 1'b0;
        miss <= 1'b0;
        data_out <= 32'h0000_0000;
        read_done <= 1'b0;
        write_done <= 1'b0;
    	busy <= 1'b0;
        
	if(i < CACHE_LINES) begin
        //for (int i = 0; i < CACHE_LINES; i++) begin
            cache_mem[i].valid_bit <= 0;
            cache_mem[i].dirty_bit <= 0;
            //cache_mem[i].tag <= 0;
            cache_mem[i].data <= 0;
        //end
	i = i + 1;
	end

	//initialization for checking the case of write hit when data is different
	cache_mem[3].valid_bit <= 1;
        cache_mem[3].dirty_bit <= 1;
        cache_mem[3].data[95:64] <= 32'hCBCB_DFDF;

        next_state <= IDLE;
    end else begin
        case (current_state)
            IDLE: begin
                if (cpu_request.read || cpu_request.write) begin
                    next_state <= PROCESS_REQUEST;
		    busy <= 1'b1;
                end else begin
                    next_state <= IDLE;
                end
            end

       

            PROCESS_REQUEST: begin
                if (cache_mem[address_fields.index].valid_bit == 1'b1 &&
                    address_fields.tag == cache_mem[address_fields.index].tag) begin
                    hit <= 1'b1;
                    miss <= 1'b0;
                    if (cpu_request.read) begin
			data_out <= cache_mem[address_fields.index].data;read_done <= 1'b1;
                    end

                    next_state <= IDLE;
                    busy <= 1'b0;
                end else begin
                    hit <= 1'b0;
                    miss <= 1'b1;
                    if (cpu_request.read) begin
                        next_state <= CACHE_ALLOCATE;
                    end else if (cpu_request.write) begin
                        // Compare the new data with the existing data
                        logic [31:0] existing_data;
                        case (address_fields.offset)
                            4'h0: existing_data = cache_mem[address_fields.index].data[31:0];
                            4'h1: existing_data = cache_mem[address_fields.index].data[63:32];
                            4'h2: existing_data = cache_mem[address_fields.index].data[95:64];
                            4'h3: existing_data = cache_mem[address_fields.index].data[127:96];
                            default: existing_data = 32'h0;
                        endcase

                        if (existing_data == data_in) begin
                            // Data is the same, no need to write back
                            cache_mem[address_fields.index].dirty_bit <= 1'b1; // Set dirty bit
                            write_done <= 1'b1;
                            next_state <= IDLE;
                        end else if (cache_mem[address_fields.index].dirty_bit == 1'b1) begin
                            next_state <= WRITE_BACK;
                        end else begin
                            next_state <= CACHE_ALLOCATE;
                        end
                    end
                end
                busy <= 1'b0;
            end

            CACHE_ALLOCATE: begin
                if (main_mem_ack) begin
                    cache_mem[address_fields.index].valid_bit <= 1'b1;
                    cache_mem[address_fields.index].dirty_bit <= 1'b1;
                    cache_mem[address_fields.index].tag <= address_fields.tag;
                    case (address_fields.offset)
                        4'h0: begin cache_mem[address_fields.index].data[31:0] <= data_in; write_done <= 1'b1;end
                        4'h1: begin cache_mem[address_fields.index].data[63:32] <= data_in; write_done <= 1'b1;end
                        4'h2: begin cache_mem[address_fields.index].data[95:64] <= data_in; write_done <= 1'b1;end
                        4'h3: begin cache_mem[address_fields.index].data[127:96] <= data_in; write_done <= 1'b1;end
                        default: $display("Invalid block offset");
                    endcase
		

                    if (cpu_request.read) begin
                        // Output the fetched data
			data_out <= cache_mem[address_fields.index].data;read_done <= 1'b1;

                        
                    end
                    next_state <= IDLE;
                end else begin
                    next_state <= CACHE_ALLOCATE;
                end
            end

            WRITE_BACK: begin
                if (main_mem_ack) begin
                    cache_mem[address_fields.index].dirty_bit <= 1'b0;
		    data_out <= cache_mem[address_fields.index].data;read_done <= 1'b1;
                    next_state <= CACHE_ALLOCATE;
                end else begin
                    next_state <= WRITE_BACK;
                end
            end

            FLUSH: begin
                
		
            end
        endcase
    end
end



// cache memory
cache_line_type cache_mem[CACHE_LINES-1:0];




endmodule
