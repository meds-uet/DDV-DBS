import cache_defs::*;

module cache_controller#(parameter DATA_WIDTH = 32,
			 parameter CACHE_LINES = 4096)(

input logic clk,
input logic reset,

input logic flush,
input logic [DATA_WIDTH-1:0]address,
input logic [DATA_WIDTH-1:0]data_in,
input logic main_mem_ack,

//defined in cache defs
input CPU_Request_type cpu_request,

output logic hit,
output logic miss,



output logic [DATA_WIDTH-1:0]data_out,
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





//logic for next state
always_ff @(posedge clk) begin
    if (reset) begin
        hit <= 1'b0;
        miss <= 1'b0;
        data_out <= 32'h0000_0000;
        read_done <= 1'b0;
        write_done <= 1'b0;
    	busy <= 1'b0;
        
        for (int i = 0; i < CACHE_LINES; i++) begin
            cache_mem[i].valid_bit <= 0;
            cache_mem[i].dirty_bit <= 0;
            //cache_mem[i].tag <= 0;
            cache_mem[i].data <= 0;
        end

	//initialization for checking the case of write hit when data is different
	/**cache_mem[0].valid_bit <= 1;
        cache_mem[0].dirty_bit <= 1;
        cache_mem[0].data[95:64] <= 32'hFFFF_FFFF;**/

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
                        case (address_fields.offset)
                            4'h0: begin data_out <= cache_mem[address_fields.index].data[31:0];read_done <= 1'b1;end
                            4'h1: begin data_out <= cache_mem[address_fields.index].data[63:32];read_done <= 1'b1;end
                            4'h2: begin data_out <= cache_mem[address_fields.index].data[95:64];read_done <= 1'b1;end
                            4'h3: begin data_out <= cache_mem[address_fields.index].data[127:96];read_done <= 1'b1;end
                            default: miss <= 1'b1;
                        endcase
                     
                    end
             
                    next_state <= IDLE;
		    busy <= 1'b0;
                end else begin
                    hit <= 1'b0;
                    miss <= 1'b1;
                    if (cpu_request.read) begin
                        next_state <= CACHE_ALLOCATE;
                    end if (cpu_request.write && cache_mem[address_fields.index].dirty_bit == 1'b1) begin
                        next_state <= WRITE_BACK;
                    end else begin
                        next_state <= CACHE_ALLOCATE;
                    end
                end
		busy <= 1'b0;
            end

            CACHE_ALLOCATE: begin
                if (main_mem_ack) begin
                    cache_mem[address_fields.index].valid_bit <= 1'b1;
                    cache_mem[address_fields.index].dirty_bit <= 1'b1;
                    cache_mem[address_fields.index].tag <= address_fields.tag;
                    // Load the new data from memory (assuming data_in contains the fetched data)
                    case (address_fields.offset)
                        4'h0: begin cache_mem[address_fields.index].data[31:0] <= data_in; write_done <= 1'b1;end
                        4'h1: begin cache_mem[address_fields.index].data[63:32] <= data_in; write_done <= 1'b1;end
                        4'h2: begin cache_mem[address_fields.index].data[95:64] <= data_in; write_done <= 1'b1;end
                        4'h3: begin cache_mem[address_fields.index].data[127:96] <= data_in; write_done <= 1'b1;end
                        default: $display("Invalid block offset");
                    endcase
		

                    if (cpu_request.read) begin
                        // Output the fetched data
                        case (address_fields.offset)
                            4'h0: begin data_out <= cache_mem[address_fields.index].data[31:0];read_done <= 1'b1;end
                            4'h1: begin data_out <= cache_mem[address_fields.index].data[63:32];read_done <= 1'b1;end
                            4'h2: begin data_out <= cache_mem[address_fields.index].data[95:64];read_done <= 1'b1;end
                            4'h3: begin data_out <= cache_mem[address_fields.index].data[127:96];read_done <= 1'b1;end
                            default: $display("Invalid block offset");
                        endcase

                        
                    end
                    next_state <= IDLE;
                end else begin
                    next_state <= CACHE_ALLOCATE;
                end
            end

            WRITE_BACK: begin
                if (main_mem_ack) begin
                    cache_mem[address_fields.index].dirty_bit <= 1'b0;
		    case (address_fields.offset)
                            4'h0: begin data_out <= cache_mem[address_fields.index].data[31:0];read_done <= 1'b1;end
                            4'h1: begin data_out <= cache_mem[address_fields.index].data[63:32];read_done <= 1'b1;end
                            4'h2: begin data_out <= cache_mem[address_fields.index].data[95:64];read_done <= 1'b1;end
                            4'h3: begin data_out <= cache_mem[address_fields.index].data[127:96];read_done <= 1'b1;end
                            default: $display("Invalid block offset");
                    endcase
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
