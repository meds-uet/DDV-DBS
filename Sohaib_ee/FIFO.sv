module FIFO #(parameter Width = 4, parameter Depth = 4)(
    input logic [Width-1:0] Data_in,
    input logic push,
    input logic pop,
    output logic [Width-1:0] Data_out,
    output logic full,
    output logic empty,

    input logic clk,
    input logic reset,
    input logic w_en,
    input logic r_en
);

    // Signal Count
    logic [$clog2(Depth)-1:0] Count; // Adjusted for SystemVerilog syntax

    // Memory array
    logic [Width-1:0] fifo [Depth-1:0];

    // Counter instance
    Counter_Updown #(
        .width($clog2(Depth)),
        .set(0)
    ) C (
        .clk(clk),
        .reset(reset),
        .up(push && !full),
        .down(pop && !empty),
        .Count(Count)
    );

    // Full and Empty flags
    assign full = (Count == Depth);
    assign empty = (Count == 0);

    // Read operation
    always_ff @(posedge clk) begin
        if (r_en) begin
            Data_out <= fifo[Count-1];
        end
    end

    // Write operation
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            for (int i = 0; i < Depth; i++) begin
                fifo[i] <= '0; // Use '0 for initialization in SystemVerilog
            end
        end else begin
            if (push && !full && w_en) begin
                fifo[Count] <= Data_in;
            end
        end
    end

endmodule
