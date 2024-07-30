module counter_8bit #(
         parameter WIDTH = 8
 )(
   input logic [WIDTH-1:0] initial_value,
   input logic clk, rstn,
   input logic up, down,
   output logic [WIDTH-1:0] count
 );
 logic [WIDTH-1:0] counter;
 always_ff @(posedge clk) begin
    if(!rstn) 
       counter <= initial_value;
	else if(up && (counter < 256)) begin
	   counter <= counter + 1;
	end
    else if(down && (counter > 0)) begin
	   counter <= counter - 1;
	end	
	else if (up && down)
	   counter <= initial_value;
 end 
 assign count = counter;

endmodule