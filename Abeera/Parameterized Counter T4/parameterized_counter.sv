module parameterized_counter #(
    parameter WIDTH = 8
)(
    input logic up,
    input logic clk,
    input logic down,
    input logic reset,
    input logic [WIDTH-1 :0] Initialvalue,
    input logic [WIDTH-1: 0] count
);

    logic [WIDTH -1: 0] counter;


    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            counter <= Initailvalue;
        end else begin
            if (up && !down) begin
                counter <= counter + 1;
            end else if (down && !up) begin
                counter <= counter - 1;
            end
        end
    end

    assign count = counter;
endmodule



        


