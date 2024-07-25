`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 

module axi_lite_slave (
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
    logic [31:0] data_reg_0;   // Data register 0 for general-purpose use
    logic [31:0] data_reg_1;   // Data register 1 for general-purpose use

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
            arready <= 1'b0;
            rvalid  <= 1'b0;
            rresp   <= 2'b00;
            read_state <= IDLE;
        end else begin
            case (read_state)
                IDLE: begin
                    arready <= 1'b1;
                    rvalid  <= 1'b0;
                    if (arvalid) begin
                        read_addr <= araddr;
                        arready <= 1'b0;
                        read_state <= TRANSFER;
                    end
                end
                TRANSFER: begin
                    case (read_addr)
                        32'h0000_0000: rdata <= control_reg;
                        32'h0000_0004: rdata <= status_reg;
                        32'h0000_0008: rdata <= data_reg_0;
                        32'h0000_000C: rdata <= data_reg_1;
                        default: begin
                            rdata <= 32'h0000_0000;
                            rresp <= 2'b10; // SLVERR
                        end
                    endcase
                    rvalid <= 1'b1;
                    read_state <= RESPONSE;
                end
                RESPONSE: begin
                    if (rready) begin
                        rvalid <= 1'b0;
                        read_state <= IDLE;
                    end
                end
            endcase
        end
    end

    // Write operation logic
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            awready <= 1'b0;
            wready  <= 1'b0;
            bvalid  <= 1'b0;
            bresp   <= 2'b00;
            write_state <= IDLE;
        end else begin
            case (write_state)
                IDLE: begin
                    awready <= 1'b1;
                    if (awvalid) begin
                        write_addr <= awaddr;
                        awready <= 1'b0;
                        write_state <= TRANSFER;
                    end
                end
                TRANSFER: begin
                    wready <= 1'b1;
                    if (wvalid) begin
                        write_data <= wdata;
                        write_strb <= wstrb;
                        wready <= 1'b0;
                        case (write_addr)
                            32'h0000_0000: if (write_strb[0]) control_reg <= write_data;
                            32'h0000_0004: if (write_strb[0]) status_reg <= write_data;
                            32'h0000_0008: if (write_strb[0]) data_reg_0 <= write_data;
                            32'h0000_000C: if (write_strb[0]) data_reg_1 <= write_data;
                            default: bresp <= 2'b10; // SLVERR
                        endcase
                        write_state <= RESPONSE;
                    end
                end
                RESPONSE: begin
                    bvalid <= 1'b1;
                    if (bready) begin
                        bvalid <= 1'b0;
                        write_state <= IDLE;
                    end
                end
            endcase
        end
    end

endmodule
