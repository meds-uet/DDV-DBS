
module Counter #(
    parameter width = 8,       // Width of the counter
    parameter set = 0    // Initial value of the counter
)(
    input logic clk,           // Clock input
    input logic reset,         // Active high reset input
    input logic up,            // Up control input
    input logic down,          // Down control input

    output logic [width-1:0] Count // Counter output
);
    
    always_ff @(posedge clk or posedge reset) begin
	
        if (reset) begin
            Count <= set;
        end else begin
            if (up && !down) begin
                
                Count <= Count + 1;
            end else if (down && !up) begin
                Count <= Count - 1;
            end else begin
                // No change in counter value if both up and down are high or both are low
                Count <= Count;
            end
        end
    end

endmodule
