module fifo_queue #(
    parameter WIDTH = 16,  
    parameter DEPTH = 32 
)(
    input logic clk,                 
    input logic reset,                
    input logic enq,                  
    input logic deq,                  
    input logic [WIDTH-1:0] enq_data, 
    output logic [WIDTH-1:0] deq_data, 
    output logic full,                
    output logic empty               
);
    logic [WIDTH-1:0] fifo_mem [DEPTH-1:0]; 
    logic [$clog2(DEPTH)-1:0] read_ptr;    
    logic [$clog2(DEPTH)-1:0] write_ptr;    
    logic [$clog2(DEPTH):0] count;        

 
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            read_ptr <= 0;
            write_ptr <= 0;
            count <= 0;
        end else begin
            if (enq && !full) begin
                fifo_mem[write_ptr] <= enq_data;
                write_ptr <= write_ptr + 1;
                count <= count + 1;
            end
            if (deq && !empty) begin
                deq_data <= fifo_mem[read_ptr];
                read_ptr <= read_ptr + 1;
                count <= count - 1;
            end
        end
    end
    
    assign full = (count == DEPTH);
    assign empty = (count == 0);

endmodule
