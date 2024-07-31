module cache#(parameter DATA_WIDTH = 32,        // data bus width
              parameter CACHE_SIZE = 256,       // cache length
              parameter OFFSET_SIZE = 4,         // cache width in words(Block size)
              parameter INDEX_SIZE = 8,
              parameter MEMORY_SIZE = 1024,     // size of the main memory in words
              parameter ADDRESS_WIDTH = 32)     // width of the address bus

             (input  logic clk_i, rst_i, 
              input  logic [ADDRESS_WIDTH-1:0] processor_addr, //address from processor to the cache
              input  logic wr_request, //processor requests to write(if 1) to cache 
              input  logic rd_request, //processor requests to read (if 1) from cache 
              input  logic [DATA_WIDTH-1:0] wr_data, //write data from processor to cache
              output logic [DATA_WIDTH-1:0] rd_data //read data to processor from cache
             );
   //cache memory
   logic [DATA_WIDTH-1:0] cache_memory [0:CACHE_SIZE-1][0:OFFSET_SIZE-1]; // Cache data storage
   logic [ADDRESS_WIDTH-OFFSET_SIZE-INDEX_SIZE-1:0] tag_memory [0:CACHE_SIZE-1]; // Tag storage
   logic [0:CACHE_SIZE-1] valid_bit_vector, dirty_bit_vector;

   // main memory storage
   logic [DATA_WIDTH-1:0] memory [0:MEMORY_SIZE-1];

   //cache memory decomposition
   logic [OFFSET_SIZE-1:0] offset;
   logic [INDEX_SIZE-1:0] index;
   logic [ADDRESS_WIDTH-OFFSET_SIZE-INDEX_SIZE-1:0] tag;
   
   //register to read data from main memory
   logic [DATA_WIDTH-1:0] rd_mem_reg; 
   
   logic cache_hit; //if 1 then hit else miss
   logic main_mem_ack; //acknowldge signal from main memory to read data for cache
   logic rd_mem_request, wr_mem_request;

   assign offset = processor_addr[OFFSET_SIZE-1:0]; 
   assign index  = processor_addr[INDEX_SIZE+OFFSET_SIZE-1:OFFSET_SIZE];
   assign tag    = processor_addr[ADDRESS_WIDTH-1:INDEX_SIZE+OFFSET_SIZE];

    //cache controller states
    typedef enum logic [2:0] {
    IDLE = 3'b000,
    READ = 3'b001,
    WRITE = 3'b010,
    FETCH_FROM_MEM  = 3'b011,
    WRITEBACK = 3'b100
    } state_t;

    state_t current_state, next_state;

/////////////////////////////////////////////////////CACHE_DATAPATH_INITIALIZATION//////////////////////////////////////
   //cache_memory initialization
   always_ff @(posedge clk_i or negedge rst_i) begin
      if(~rst_i)begin
         rd_data   <= '0;
         for (int i = 0; i<CACHE_SIZE; i++)begin
            valid_bit_vector[i] <= 0;
            dirty_bit_vector[i] <= 0;
            tag_memory[i]       <= 0;
            for (int j = 0; j<OFFSET_SIZE; j++)begin
               cache_memory[i][j] <= 32'b0;
            end
         end
      end
   end  

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


/////////////////////////////////////////////////////CACHE_CONTROLLER/////////////////////////////////////////////////
    
   //Current state register
   always_ff @(posedge clk_i or negedge rst_i) begin
         if(~rst_i) begin
            current_state  <= IDLE;
            cache_hit      <= 0;
            rd_mem_request <= 0;
            wr_mem_request <= 0;
         end
        else begin 
            current_state <= next_state;
        end
   end

   always @* begin
      next_state     = current_state;

      case(current_state)
      IDLE: begin
         if(wr_request) begin
            next_state = WRITE;
         end
         else if(rd_request)begin
            next_state = READ;
         end
         else begin
            next_state = IDLE;
         end
      end

      READ: begin
         if(cache_hit) begin
            next_state = IDLE;
         end
         else begin
            next_state = FETCH_FROM_MEM;
         end
      end

      FETCH_FROM_MEM: begin
         if(main_mem_ack)begin
            next_state = IDLE;
         end
         else if(!main_mem_ack)begin
            next_state = FETCH_FROM_MEM;
         end
      end

      WRITE: begin
         if(cache_hit) begin
            next_state = IDLE;
         end
         else begin
            next_state = WRITEBACK;
         end
      end

      WRITEBACK: begin
         if(valid_bit_vector[index] == 0 & main_mem_ack) begin
            next_state = IDLE;
         end

         else if(valid_bit_vector[index] == 0 & main_mem_ack == 0) begin
            next_state = WRITEBACK;
         end

         else if(valid_bit_vector[index] & main_mem_ack) begin
            next_state = IDLE;
         end

         else if(valid_bit_vector[index] & main_mem_ack == 0) begin
            next_state = WRITEBACK;
         end
      end

      endcase
   end

   always_ff @(posedge clk_i)begin
      if(current_state == IDLE)begin
         if(rd_request)begin
            cache_hit  <= (valid_bit_vector[index] & (tag_memory[index] == tag));
         end
         else if(wr_request)begin
            cache_hit  = (valid_bit_vector[index] & (tag_memory[index] == tag));
         end
      end

      else if(current_state == READ)begin
         if(cache_hit)begin
            rd_data <= cache_memory[index][offset[3:2]];
            valid_bit_vector[index] <= 1; 
         end
         else begin
            rd_mem_request <= 1;
            tag_memory[index] <= tag;
         end        
      end

      else if(current_state == FETCH_FROM_MEM & main_mem_ack)begin
         for(int k = 0; k<OFFSET_SIZE; k++)begin
            cache_memory[index][k] <= memory[{tag, index} * OFFSET_SIZE + k]; // Loading the complete block
            $display("Loading cache_memory[%0d][%0d] <= memory[%0d]", index, k, {tag, index} * OFFSET_SIZE + k);
         end
         rd_data <= rd_mem_reg;
         tag_memory[index] <= tag;
         valid_bit_vector[index] <= 1;
         rd_mem_request <= 0;
      end

      else if(current_state == WRITE) begin
         if(cache_hit)begin
            cache_memory[index][offset] <= wr_data;
            valid_bit_vector[index] <= 1;
            dirty_bit_vector[index] <= 1;
            wr_mem_request          <= 0;
         end

         else begin
            wr_mem_request <= 1;
            tag_memory[index] <= tag;
         end
      end

      else if(current_state == WRITEBACK)begin
         if(valid_bit_vector[index] == 0 & main_mem_ack) begin
            for(int k = 0; k<OFFSET_SIZE; k++)begin
               cache_memory[index][k] <= memory[{tag, index} * OFFSET_SIZE + k]; // Loading the complete block
               $display("Loading cache_memory[%0d][%0d] <= memory[%0d]", index, k, {tag, index} * OFFSET_SIZE + k);
            end
            cache_memory[index][offset] <= wr_data;
            tag_memory[index] <= tag;
            valid_bit_vector[index] <= 1;
            dirty_bit_vector[index] <= 1;
            wr_mem_request <= 0;
         end

         else if(valid_bit_vector[index] & main_mem_ack) begin
            for(int k = 0; k<OFFSET_SIZE; k++)begin
               cache_memory[index][k] <= memory[{tag, index} * OFFSET_SIZE + k]; // Loading the complete block
               $display("Loading cache_memory[%0d][%0d] <= memory[%0d]", index, k, {tag, index} * OFFSET_SIZE + k);
            end
            cache_memory[index][offset] <= wr_data;
            tag_memory[index] <= tag;
            valid_bit_vector[index] <= 1;
            dirty_bit_vector[index] <= 1;
            wr_mem_request <= 0;
         end
      end

   end

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////MAIN_MEMORY//////////////////////////////////////////////////////
   initial begin
      for (int i = 0; i < MEMORY_SIZE; i++) begin  // Initializing memory
            memory[i] = i+1;
      end
   end
      
   always_ff @(posedge clk_i or negedge rst_i) begin
      if(~rst_i)begin
         main_mem_ack <= 0;
         rd_mem_reg   <= 32'b0;
      end
      else if(rd_mem_request)begin
         main_mem_ack <= 1;
         rd_mem_reg   <=memory[{tag, index} * OFFSET_SIZE];
      end

      else if(wr_mem_request)begin
         if(valid_bit_vector[index] == 0) begin
            main_mem_ack <= 1;
         end

         else begin
            main_mem_ack <= 1;
            for(int k = 0; k<OFFSET_SIZE; k++)begin
               memory[{tag_memory[index], index} * OFFSET_SIZE + k] <= cache_memory[index][k]; // Loading the complete block
               $display("Loading cache_memory[%0d][%0d] <= memory[%0d]", index, k, {tag, index} * OFFSET_SIZE + k);
            end
         end
      end

      else begin
         main_mem_ack <= 0;
      end    
   end

endmodule