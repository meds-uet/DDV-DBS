module up_down_counter #(parameter COUNTER_WIDTH = 32) (input clk,
                        input rst,
                        input count_up_down, // 1b => count up, 0b => count down   
                        output reg [COUNTER_WIDTH-1:0] count_val
                        );
always @(posedge clk or negedge rst) begin //{
  if (!rst) 
    count_val <= 32'b0;
  else if (count_up_down == 1'b1)
    count_val <= count_val + 1'b1;
  else 
    count_val <= count_val - 1'b1;
end //}
endmodule

