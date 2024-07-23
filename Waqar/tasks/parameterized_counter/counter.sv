module parameterized_counter #(
    parameter WIDTH = 8  // Width of the counter
)(
    input logic clk,                   // Clock signal
    input logic reset,                 // Reset signal
    input logic enable,                // Enable signal
    input logic up_down,               // Up/Down control (1 for up, 0 for down)
    input logic [WIDTH-1:0] init_value,// Initial value to set the counter
    output logic [WIDTH-1:0] count     // Counter value
);

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            count <= init_value; 
        end else if (enable) begin
            if (up_down) begin
                count <= count + 1; // Incrementing the counter
            end else begin
                count <= count - 1; // Decrementing the counter
            end
        end
    end

endmodule
