module Shift_Register#(parameter WIDTH = 3)(

input clk,
input reset,

input data_in,

output logic data_out

);


logic [WIDTH:0]shift_register;


always_ff @(posedge clk) begin
        if (reset) begin
            shift_register <= 'b0; 
        end
        
        else if(!reset) begin
            shift_register <= {shift_register[WIDTH-2:0], data_in};
        end
        
        else begin
            shift_register <= {shift_register[WIDTH-2:0], data_in};
        end
end



always_ff @(posedge clk) begin

if(reset) begin
    data_out <= 'b0;
end

else if(!reset) begin
     data_out <= shift_register[WIDTH-1];
 end


else begin
    data_out <= shift_register[WIDTH-1];
end



end




endmodule
