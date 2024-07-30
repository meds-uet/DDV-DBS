module L2P_Converter(X, clk, rstn, Y);
  input logic X;
  input logic clk, rstn;
  output logic Y;
  
  
  typedef enum logic [1:0] {S0, S1, S2} statetype;
  statetype curr_state, next_state;  
 
  always_ff @(posedge clk) begin
     if(!rstn)
	    curr_state <= S0;
	 else
	    curr_state <= next_state;  
  end
 
 always_comb begin
   case(curr_state)
     S0: begin
        if(X)
		  next_state = curr_state;
		else
		 next_state = S1;
      end 	 
     S1: begin
        if(X)
		  next_state = S2;
		else
		 next_state = curr_state;
      end
     S2: begin
        if(X)
		  next_state = S0;
		else
		  next_state = S1;
      end
     default: next_state = S0;  	 
   endcase	 
 end 
 
 always_comb begin
    case(curr_state):
       S0: Y = 0;  
       S1: Y = 0;  
       S2: Y = 1;
   	  default: Y = 1'bx;
    endcase	 
 end
 
endmodule

