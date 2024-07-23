module fifo#(parameter FIFO_WIDTH = 128,
             parameter DATA_WIDTH = 8)

            (input  logic clk,
             input  logic rst_n,
             input  logic [7:0] d_i,
             input  logic wr_en,
             input  logic rd_en,
             output logic [7:0] d_o,
             output logic full,
             output logic empty
            );

    typedef enum logic [2:0]
    {IDLE  = 3'b000,
     READ  = 3'b001,
     WRITE = 3'b010,
     FULL  = 3'b011,
     EMPTY = 3'b100} state_t;

    state_t current_state, next_state;

    //state registers
    reg [DATA_WIDTH-2:0] fifo_count;
    reg [DATA_WIDTH-2:0] wr_addr, rd_addr;
    reg [DATA_WIDTH-1:0] fifo_mem [FIFO_WIDTH-1:0];

    always_ff @(posedge clk)begin
        if(~rst_n)begin
            current_state <= IDLE;
            wr_addr       <= 0;
            rd_addr       <= 0;
            fifo_count    <= 0;
            end
        else
            current_state <= next_state;
    end

    always_comb begin
       next_state = current_state;

        case(current_state)

        IDLE: begin

            if(!wr_en & !rd_en)
                next_state = IDLE;

            else if(wr_en & !full)
                next_state = WRITE;

            else if(rd_en & !empty)
                next_state = READ;

            else if(full)
                next_state = FULL;

            else if(empty)
                next_state = EMPTY;
            
        end

        WRITE: next_state = IDLE;

        READ:  next_state = IDLE;

        FULL: begin
            if(rd_en & !empty)
                next_state = READ;
        end 

        EMPTY: begin
            if(wr_en & !full)
                next_state = WRITE;
        end 
        endcase
    end
    
    //synchronous write(Enqueue)
    always_ff@(posedge clk)begin
        if(current_state == WRITE)begin
            fifo_mem[wr_addr] <= d_i;
            wr_addr           <= (wr_addr+1) % FIFO_WIDTH;
            fifo_count        <= fifo_count + 1;
        end
    end
    
    //asynchronous read(Dequeue)
    always_ff@(posedge clk or negedge rst_n)begin
        if(current_state == READ)begin
            d_o         <= fifo_mem[rd_addr];
            rd_addr     <= (rd_addr+1) % FIFO_WIDTH;
            fifo_count  <= fifo_count - 1;
        end
    end

    assign full  = (fifo_count == FIFO_WIDTH-1) ;
    assign empty = (fifo_count == 0) ;

endmodule