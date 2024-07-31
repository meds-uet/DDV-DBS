module axi_lite_slave_memory (
    // Global signals
    input  logic        aclk,    // AXI clock signal
    input  logic        aresetn, // AXI active-low reset signal
    
    // Read address channel
    input  logic [31:0] araddr,  // Read address
    input  logic        arvalid, // Read address valid signal (master is ready to transfer)
    output logic        arready, // Read address ready signal (slave is ready to accept the address)
    
    // Read data channel
    output logic [31:0] rdata,   // Read data being transferred from slave to master
    output logic [1:0]  rresp,   // Read response, indicating the status of the read transfer
    output logic        rvalid,  // Read valid signal (slave is providing valid read data)
    input  logic        rready,  // Read ready signal (master is ready to accept the read data)
    
    // Write address channel
    input  logic [31:0] awaddr,  // Write address
    input  logic        awvalid, // Write address valid signal (master is ready to transfer)
    output logic        awready, // Write address ready signal (slave is ready to accept the address)
    
    // Write data channel
    input  logic [31:0] wdata,   // Write data being transferred from master to slave
    input  logic [3:0]  wstrb,   // Write strobe, indicates which byte lanes to update
    input  logic        wvalid,  // Write valid signal (master is providing valid write data)
    output logic        wready,  // Write ready signal (slave is ready to accept the write data)
    
    // Write response channel
    output logic [1:0]  bresp,   // Write response, indicating the status of the write transfer
    output logic        bvalid,  // Write response valid signal (slave has valid write response)
    input  logic        bready   // Write response ready signal (master is ready to accept the response)
);

    // Register declarations
    logic [31:0] control_reg;  // Control register for configuration
    logic [31:0] status_reg;   // Status register for reporting device state

    // Memory array (e.g., 256 x 32-bit)
    logic [31:0] memory [255:0];

    // Internal signals
    logic [31:0] read_addr;   // Latched read address
    logic [31:0] write_addr;  // Latched write address
    logic [31:0] write_data;  // Latched write data
    logic [3:0]  write_strb;  // Latched write strobe

    // FSM states for read and write operations
    typedef enum logic [1:0] {IDLE, TRANSFER, RESPONSE} state_t;
    state_t read_state, write_state;

    // Read operation logic
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            read_state <= IDLE;
            arready <= 0;
            rdata <= 0;
            rresp <= 2'b00; // OKAY response
            rvalid <= 0;
        end else begin
            case (read_state)
                IDLE: begin
                    arready <= 1;
                    rvalid <= 0;
                    if (arvalid && arready) begin
                        read_addr <= araddr;
                        read_state <= TRANSFER;
                    end
                end
                TRANSFER: begin
                    arready <= 0;
                    case (read_addr)
                        32'h0000_0000: rdata <= control_reg;
                        32'h0000_0004: rdata <= status_reg;
                        default: begin
                            if (read_addr >= 32'h0000_0010 && read_addr <= 32'h0000_00FF) begin
                                rdata <= memory[(read_addr - 32'h0000_0010) >> 2];
                                rresp <= 2'b00; // OKAY response
                            end else begin
                                rdata <= 32'hDEAD_BEEF; // Invalid address
                                rresp <= 2'b10; // SLVERR response
                            end
                        end
                    endcase
                    read_state <= RESPONSE;
                end
                RESPONSE: begin
                    rvalid <= 1;
                    if (rvalid && rready) begin
                        read_state <= IDLE;
                    end
                end
            endcase
        end
    end

    // Write operation logic
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            write_state <= IDLE;
            awready <= 0;
            wready <= 0;
            bvalid <= 0;
            bresp <= 2'b00; // OKAY response
        end else begin
            case (write_state)
                IDLE: begin
                    awready <= 1;
                    wready <= 0;
                    bvalid <= 0;
                    if (awvalid && awready) begin
                        write_addr <= awaddr;
                        write_state <= TRANSFER;
                    end
                end
                TRANSFER: begin
                    awready <= 0;
                    wready <= 1;
                    if (wvalid && wready) begin
                        write_data <= wdata;
                        write_strb <= wstrb;
                        if (write_addr >= 32'h0000_0010 && write_addr <= 32'h0000_00FF) begin
                            integer i;
                            for (i = 0; i < 4; i = i + 1) begin
                                if (write_strb[i]) begin
                                    memory[(write_addr - 32'h0000_0010) >> 2][i*8 +: 8] <= write_data[i*8 +: 8];
                                end
                            end
                            bresp <= 2'b00; // OKAY response
                        end else begin
                            case (write_addr)
                                32'h0000_0000: if (write_strb[0]) control_reg <= write_data;
                                32'h0000_0004: if (write_strb[0]) status_reg <= write_data;
                                default: bresp <= 2'b10; // SLVERR response
                            endcase
                        end
                        write_state <= RESPONSE;
                    end
                end
                RESPONSE: begin
                    wready <= 0;
                    bvalid <= 1;
                    if (bvalid && bready) begin
                        write_state <= IDLE;
                    end
                end
            endcase
        end
    end

endmodule
