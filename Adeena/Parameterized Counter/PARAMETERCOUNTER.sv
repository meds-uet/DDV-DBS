module parameterized_counter #(
    parameter WIDTH = 8  
)(
    input wire clk,           
    input wire reset,        
    input wire up,            // Up control signal
    input wire down,          // Down control signal
    input wire [WIDTH-1:0] init_val, // Initial value input
    output reg [WIDTH-1:0] count    
);

    // Counter logic
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            count <= init_val;  // Reset counter to the initial value
        end else if (up) begin
            count <= count + 1; // Increment counter
        end else if (down) begin
            count <= count - 1; // Decrement counter
        end
    end

endmodule
