 module fifo #(
                parameter WIDTH = 8,
			    parameter DEPTH = 3
              )( 
			    input logic clk, rst_n, wr_en, rd_en, 
                input logic [WIDTH-1:0] data_in,
                output logic full, empty,
			    output logic [WIDTH-1:0] data_out
			    );

 
 logic [WIDTH-1:0] fifo[0:DEPTH];
 logic fifo_full, fifo_empty;
 logic [2:0] rd_ptr, wr_ptr;
 logic [1:0] fifo_counter = 0;
 logic [WIDTH-1:0] fifo_out;
 
 parameter idle_state = 0;
 parameter wr_state = 1;
 parameter rd_state = 2;
 parameter empty_state = 3;
 parameter full_state = 4;
 
  
 logic [2:0] curr_state, next_state;
 //current state block
 always_ff @(posedge clk or negedge rstn) begin
    if(!rst_n) 
	    curr_state <= idle_state;
    else 
        curr_state <= next_state;	
 end
 //next state block
 always_comb begin
    case(curr_state)
	  idle:  begin
	     if(!wr_en && !rd_en) begin
	          full = 0;
              empty = 0;
              data_out = 0;
              wr_ptr = 0;
              rd_ptr = 0;	
			  next_state <= curr_state;
          end
		  else if (wr_en && rd_en)
		      next_state = curr_state;
          else if (wr_en) begin
             next_state = wr_state;	
		   end
          else if (rd_en)
              next_state = rd_state;		  
	   end
	  wr_state:  begin
	      
	    end
	  rd_state:  begin
	      
	    end
	  empty_state:  begin
	      
	    end
	  full_state: begin
	      
	    end
	  default:
       	  
	endcase    
 end
 //output logic
 always_comb begin
 
 
 end 
 
 endmodule			