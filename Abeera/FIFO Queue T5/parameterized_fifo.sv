module parameterized_fifo #(
    parameter DEPTH = 16, //This also means number of elements it can  depth wise
    parameter WIDTH = 8 //This means the width that is 8 max
)(
    input logic en,
    input logic deq,
    input logic clk,
    input logic reset,
    input logic [WIDTH - 1:0] datain,
    output logic [WIDTH -1: 0] dataout,
    output logic full,
    output logic empty

);

localparam ADDR_WIDTH = $clog2(DEPTH);
logic [WIDTH-1:0] fifo_mem [0: 15];
logic [ADDR_WIDTH-1 :0] wrptr, rdptr;
logic [ADDR_WIDTH:0] counter;

assign full = ( counter == DEPTH);
assign empty = (counter == 0);

//Enque operation

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        wrptr <= 0;
    end else if (en && !full) begin
        fifo_mem[wrptr] <= datain;
        wrptr <= wrptr + 1;
    end
end

// deque

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        rdptr <= 0;
    end else if (deq && !empty) begin
       dataout <= fifo_mem[rdptr];
       rdptr <= rdptr + 1;
end
end

//fifo_count management 
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        count <= 0;
    end else begin
        case({en, deq})
        2'b01: count <= count - 1; // only deq
        2'b10: count <= count + 1; // only eq
        2'b11: count <= count; // both so same 
        default: count <= count;
        endcase
    end
end
endmodule


