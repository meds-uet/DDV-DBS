`include "memory.sv"
module cache_ctrl(
    // Controller inputs
    input logic clk,
    input logic rst,
    input logic cpu_request,
    input logic [31:0] address,
    input logic [31:0] write_data,
    input logic read,
    input logic write,
    input logic cache_flush,
    // Controller outputs
    output logic [7:0] read_data,
    output logic cache_hit,
    output logic [2:0] cnt,
    output logic flush_done
);

   // Instantiate the memory module
   memory #(10ns) mem(
      .address(CTM_addr),
        .write_data(MTC_wdata),
        .m_read(mem_rd),
        .m_write(mem_wr),
        .read_data(MTC_rdata)
    );

    // Cache parameters
    parameter SIZE = 64;  // Number of cache lines
  	int status = 0, i = 0;;
    logic main_mem_ack, main_mem_ack_fl;
    logic flush, fd, mem_rd, mem_wr;
    logic [23:0] CTM_addr;
    logic [31:0] MTC_wdata, MTC_rdata;

    // Cache storage
    logic [31:0] cache_data [0:SIZE-1];
    logic [23:0] cache_tag [0:SIZE-1];
    logic cache_valid [0:SIZE-1];
    logic cache_dirty [0:SIZE-1];

    // Address fields
    logic [23:0] tag;
    logic [5:0] index; // Assuming CACHE_SIZE = 64, so 6 bits for index
    logic [1:0] offset;

    // Extract address fields
    assign tag = address[31:8];
    assign index = address[7:2];
    assign offset = address[1:0];
  

    // States declaration
    typedef enum logic [2:0] {
        IDLE, 
        PROCESS_REQ, 
        CACHE_ALLOCATE, 
        WRITEBACK, 
        FLUSH
    } state_t;
    state_t pr_state, nx_state;

    // Clock and reset block
    always @(posedge clk) begin
        if (rst) begin
            pr_state <= IDLE;
        end else begin
            pr_state <= nx_state;
        end
    end

    // FSM Inputs and Transitions
  always@(*) begin
        case (pr_state)
            IDLE: begin
                if (cpu_request && !cache_flush)
                    nx_state = PROCESS_REQ;
                else if (!cpu_request && cache_flush)
                    nx_state = FLUSH;
                else
                    nx_state = pr_state;
            end
            PROCESS_REQ: begin
                if (cache_valid[index] && (tag == cache_tag[index])) begin
                    nx_state = IDLE;
                end else begin
                    if (cache_dirty[index]) begin
                        nx_state = WRITEBACK;
                    end else begin
                        nx_state = CACHE_ALLOCATE;
                    end
                end
            end
            CACHE_ALLOCATE: begin
                if (main_mem_ack)
                    nx_state = PROCESS_REQ;
                else
                    nx_state = pr_state;
            end
            WRITEBACK: begin
                if (main_mem_ack && !flush)
                    nx_state = CACHE_ALLOCATE;
                else if (main_mem_ack && flush)
                    nx_state = FLUSH;
                else
                    nx_state = pr_state;
            end
            FLUSH: begin
              if (fd == 1)
                    nx_state = IDLE;
              else
                    nx_state = WRITEBACK;
            end
            default: nx_state = IDLE;
        endcase
    end

    // FSM Outputs for controller
    always @(posedge clk) begin
        if (rst) begin
            for (int i = 0; i < SIZE; i++) begin
                cache_valid[i] <= 0;
                cache_dirty[i] <= 0;
            end
        end else begin
            case (pr_state)
                IDLE: begin
                    main_mem_ack <= 1'b0;
                    main_mem_ack_fl <= 1'b0;
                    flush <= 1'b0;
                    mem_rd <= 1'b0;
                    mem_wr <= 1'b0;
                    cache_hit <= 1'b0;
                    flush_done <= 1'b0;
                    cnt <= 3'd0;
                    read_data <= 32'd0;
                    status <= 0;
                end
                PROCESS_REQ: begin
                    cnt <= 3'd1;
                    if (cache_valid[index] && (tag == cache_tag[index])) begin
                        cache_hit <= 1'b1;
                        if (read) begin
                          case(offset)
                            2'b00 :  read_data <= cache_data[index][7:0];
                            2'b01 :  read_data <= cache_data[index][15:8];
                            2'b10 :  read_data <= cache_data[index][23:16];
                            2'b11 :  read_data <= cache_data[index][31:24];
                          default :  read_data <= 8'd0;
                          endcase
                        end else if (write) begin
                            cache_data[index] <= write_data;
                            cache_dirty[index] <= 1'b1;
                        end
                    end else begin
                        cache_hit <= 1'b0;
                    end
                end
                CACHE_ALLOCATE: begin
                    cnt <= 3'd2;
                    mem_rd <= 1'b1;
                    CTM_addr <= tag;
                    cache_tag[index] <= tag;
                    cache_data[index] <= MTC_rdata; 
                    cache_valid[index] <= 1'b1;
                    main_mem_ack <= 1'b1;
                end
                WRITEBACK: begin
                    cnt <= 3'd3;
                    if (!flush) begin
                        mem_wr <= 1'b1;
                        CTM_addr <= cache_tag[index];
                        MTC_wdata <= cache_data[index];
                        cache_dirty[index] <= 0;
                        main_mem_ack <= 1'b1;
                    end
                  	else if (flush) begin
                        mem_wr <= 1'b1;
                        CTM_addr <= cache_tag[status];
                        MTC_wdata <= cache_data[status];
                        cache_dirty[status] <= 0;
                        main_mem_ack <= 1'b1;
                    end
                end
                FLUSH: begin
                    cnt <= 3'd4;
                  	for (i = status ; i < SIZE; i++) begin
                      cache_valid[i] <= 0;
                      if(cache_dirty[i] == 1) begin
                        status <= i;
                        fd <= 0;
                        break;
                      end
                      else begin
                        fd <= 1;
                        continue;
                      end
                        
                    end
                  if(fd) begin
                      flush_done <= 1'b1;
                      flush <= 1'b0;
                  end
                  else begin
                      flush_done <= 1'b0;
                      flush <= 1'b1;
                  end
                end
                default: nx_state = IDLE;
            endcase
        end
    end

endmodule


