module counter #(
parameter WIDTH = 8
)(
     
     input logic clk,
     input logic reset,
     input logic up,
     input logic down,
     input logic [WIDTH-1:0] init_value,
     input logic enable,
     output logic[WIDTH-1:0] counter
);



always_ff@(posedge clk or posedge reset)begin
    if (reset) begin
        counter<=0;
    end else if(enable) begin
        counter <= init_value;
    end else begin
      if(up & !down) begin
        counter <= counter + 1;
      end else if(down & !up & counter != 0) begin
        counter <= counter - 1;
      end
    end 
 end
endmodule

