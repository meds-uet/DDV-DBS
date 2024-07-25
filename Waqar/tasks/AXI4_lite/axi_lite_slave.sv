module axi_lite_slave#(parameter MEMORY_SIZE = 1024,
                       parameter DATA_WIDTH  = 32,
                       parameter ADDR_WIDTH  = 32)
(
    // Global signals
    input  logic        aclk,    // AXI clock signal
    input  logic        aresetn, // AXI active-low reset signal
    
    // Read address channel
    input  logic [ADDR_WIDTH-1:0] araddr,  // Read address
    input  logic        arvalid, // Read address valid signal (master is ready to transfer)
    output logic        arready, // Read address ready signal (slave is ready to accept the address)
    
    // Read data channel
    output logic [DATA_WIDTH-1:0] rdata,   // Read data being transferred from slave to master
    output logic [1:0]  rresp,   // Read response, indicating the status of the read transfer
    output logic        rvalid,  // Read valid signal (slave is providing valid read data)
    input  logic        rready,  // Read ready signal (master is ready to accept the read data)
    
    // Write address channel
    input  logic [ADDR_WIDTH-1:0] awaddr,  // Write address
    input  logic        awvalid, // Write address valid signal (master is ready to transfer)
    output logic        awready, // Write address ready signal (slave is ready to accept the address)
    
    // Write data channel
    input  logic [DATA_WIDTH-1:0] wdata,   // Write data being transferred from master to slave
    input  logic [3:0]  wstrb,   // Write strobe, indicates which byte lanes to update
    input  logic        wvalid,  // Write valid signal (master is providing valid write data)
    output logic        wready,  // Write ready signal (slave is ready to accept the write data)
    
    // Write response channel
    output logic [1:0]  bresp,   // Write response, indicating the status of the write transfer
    output logic        bvalid,  // Write response valid signal (slave has valid write response)
    input  logic        bready   // Write response ready signal (master is ready to accept the response)
);

    // Register declaration
    logic [DATA_WIDTH-1:0] data_reg_0;   // Data register 0 for READ-purpose 
    logic [DATA_WIDTH-1:0] data_reg_1;   // Data register 1 for WRITE-purpose

    logic [DATA_WIDTH-1:0] memory [MEMORY_SIZE-1:0];   //memory for read write purposes

    // Internal signals
    logic [ADDR_WIDTH-1:0] read_addr;   // Latched read address
    logic [ADDR_WIDTH-1:0] write_addr;  // Latched write address
    logic [DATA_WIDTH-1:0] write_data;  // Latched write data
    logic [3:0]  write_strb;  // Latched write strobe

    // FSM states for read and write operations
    typedef enum logic [1:0] {IDLE, TRANSFER, RESPONSE} state_t;
    state_t read_state, write_state;

    initial begin
        for(int i = 0; i<MEMORY_SIZE; i++)begin
            memory[i] = i+4; 
        end
    end
    
    //READ operation 
    always_ff @(posedge aclk or negedge aresetn) begin
        if(~aresetn) begin
            read_state <= IDLE;
            read_addr  <= '0;
            arready    <= 0;
            rresp      <= '0;
            rdata      <= '0;
            rvalid     <= 0;
            data_reg_1 <= '0;
        end
        else begin
            case(read_state)

            IDLE: begin
                if(arvalid & arready) begin
                    read_addr  <= araddr;
                    read_state <= TRANSFER;
                end

                else begin
                    arready    <= 1;
                    read_state <= IDLE;
                end
            end

            TRANSFER: begin
                if(arvalid == 0) begin
                    arready    <= 0;
                    data_reg_0 <= memory[read_addr];
                    rvalid     <= 1;
                    read_state <= RESPONSE;
                end
            end

            RESPONSE: begin
                if(rvalid & rready) begin
                    rdata  <= data_reg_0;
                    rresp  <= 2'b00; //OKAY RESPONSE
                    rvalid <= 0;
                    read_state <= IDLE;
                end

                else begin
                    read_state <= RESPONSE;
                end
            end

            endcase
        end
    end

    //WRITE operation
    always_ff @(posedge aclk or negedge aresetn) begin
        if(~aresetn) begin
            write_state <= IDLE;
            awready     <= 0;
            wready      <= 0;
            bresp       <= 0;
            bvalid      <= 0;
        end

        else begin
            case(write_state)

            IDLE: begin
                if(awvalid) begin
                    write_addr  <= awaddr;
                    awready     <= 1;
                    write_state <= TRANSFER;
                end

                else begin
                    write_state <= IDLE;
                end
            end

            TRANSFER: begin
                if(wvalid & wready) begin
                    write_strb  <= wstrb;
                    data_reg_1  <= wdata;
                    /*case(write_strb)
                    4'b0001: data_reg_1[7:0]   <= wdata[7:0];
                    4'b0010: data_reg_1[15:8]  <= wdata[15:8];
                    4'b0100: data_reg_1[23:16] <= wdata[23:16];
                    4'b1000: data_reg_1[31:24] <= wdata[31:24];
                    endcase*/
                    //awready <= 0;
                    //wready  <= 0;
                    write_state <= RESPONSE;
                end

                else begin
                    wready <= 1;
                    write_state <= TRANSFER;
                end
            end

            RESPONSE: begin
                if(bready) begin
                    memory[write_addr] <= data_reg_1;
                    /*case (write_strb)
                    4'b0001: memory[write_addr][7:0]   <= data_reg_1[7:0];
                    4'b0010: memory[write_addr][15:8]  <= data_reg_1[15:8];
                    4'b0100: memory[write_addr][23:16] <= data_reg_1[23:16];
                    4'b1000: memory[write_addr][31:24] <= data_reg_1[31:24];
                    endcase*/
                    bvalid <= 1;
                    awready <= 0;
                    wready  <= 0;
                    if(bvalid) begin
                        bresp <= 2'b00;
                    end
                    write_state <= IDLE;
                end
                else begin
                    write_state <= RESPONSE;
                end
            end

            endcase
        end
    end

endmodule
