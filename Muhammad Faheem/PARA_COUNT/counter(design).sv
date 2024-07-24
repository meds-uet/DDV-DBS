module counter #(parameter size = 8) (
  input logic clk,
  input logic reset,
  input logic direction, // New single input for counting direction
  input logic [size-1:0] initial_value,
  output logic [size-1:0] count
);
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      count <= initial_value;
    end else begin
      if (direction) begin
        count <= count + 1'b1; // Count up
      end else begin
        count <= count - 1'b1; // Count down
      end
    end
  end
endmodule