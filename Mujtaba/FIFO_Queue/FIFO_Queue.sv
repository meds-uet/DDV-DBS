module FIFO_Queue#(parameter DEPTH = 16,
                   parameter DATA_WIDTH = 8)(

//Inputs
input clk,
input reset,

input read_en,
input write_en,

input [DATA_WIDTH - 1 : 0] data_in,


//Ouputs
output logic [DATA_WIDTH - 1 : 0] data_out,
output logic full,
output logic empty


);


//FIFO memory
logic [DATA_WIDTH - 1 : 0] FIFO_queue [0 : DEPTH - 1];

//Read / Write Pointers
logic [DATA_WIDTH - 1 : 0] read_ptr = 0;
logic [DATA_WIDTH - 1 : 0] write_ptr = 0;

//FIFO Count
logic [DATA_WIDTH - 1 : 0] fifo_count;



//Enqueue
always_ff @(posedge clk) begin

if(reset) begin
    write_ptr <= 0;
    fifo_count <= 0;
end

else if(write_en && !full) begin
    write_ptr <= write_ptr + 1;
    fifo_count <= fifo_count + 1;
    FIFO_queue[write_ptr] <= data_in;

end


end



//Dequeue
always_ff @(posedge clk) begin

if(reset) begin
    read_ptr <= 0;
end

else if(read_en && !empty) begin
    read_ptr <= (read_ptr == DEPTH - 1) ? 0 : read_ptr + 1;
    fifo_count <= fifo_count - 1;

end


end



//Output data on dequeue operation
assign data_out = FIFO_queue[read_ptr];


//Flags
assign full = (fifo_count == DEPTH);
assign empty = (fifo_count == 0);




endmodule
