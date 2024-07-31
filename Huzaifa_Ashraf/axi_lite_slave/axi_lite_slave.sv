`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/09/2024 08:13:56 PM
// Design Name: 
// Module Name: axi_lite_slave
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module axi_lite_slave (
    // Global signals
    input  logic        aclk,    // AXI clock signal
    input  logic        aresetn, // AXI active-low reset signal
    
    // Read address channel
    input  logic [31:0] araddr,  // Read address
    input  reg          arvalid, // Read address valid signal (master is ready to transfer)
    output logic        arready, // Read address ready signal (slave is ready to accept the address)
    
    // Read data channel
    output logic [31:0] rdata,   // Read data being transferred from slave to master
    output logic [1:0]  rresp,   // Read response, indicating the status of the read transfer
    output logic        rvalid,  // Read valid signal (slave is providing valid read data)
    input  reg          rready,  // Read ready signal (master is ready to accept the read data)
    
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

    // Read operation logic here
    /*
    Logic:
    * Reset all read-related signals and state
    * In read state:
    	at IDLE state,If arvalid then Latch the read address and transition to TRANSFER state,
    	at TRANSFER state, Select the appropriate register based on the address  or update response based on invalid address
    	at RESPONSE state, Complete the transfer and return to IDLE state
    */
    always_ff @(posedge aclk or negedge aresetn) begin
        if(!aresetn)begin 
            arvalid <= 1'b0;
            rready <= 1'b0;
            read_addr = 32'b0;
            rdata = 32'b0;
            rresp <= 2'b0;
            read_state = IDLE;
        end 
        else begin
        case(read_state)
        IDLE:
        begin 
        if(arvalid)begin 
         arready <= 1'b1;
         read_addr <= araddr;
         read_state <= TRANSFER;
        end
        end
        TRANSFER:
        begin 
        arready <= 1'b0;
        case(read_addr)
          32'h00000000: rdata <= control_reg;
          32'h000000004: rdata <= status_reg;
          32'h000000008: rdata <= data_reg_0;
          32'h0000000C: rdata <= data_reg_1;
          default: rdata <= 32'hDEADBEEF;        
        endcase
        
        rresp <= 2'b00;
        rready = 1'b1;
        read_state <= RESPONSE;       
        end
        RESPONSE:if(rready)begin
         rvalid <= 1'b0;
         read_state <= IDLE;
         end 
        
        endcase
        end
	

    end

    // Write operation logic
    /* 
    Logic:
    * If reset, Reset all write-related signals and state
    * If write state, and at IDLE state, Latch write address and data, transition to TRANSFER state
    * If write state, and at TRABSFER state, Perform the write operation based on the address
    * If write state, and at RESPONSE state, Complete the transfer and return to IDLE state
    */
    always_ff @(posedge aclk or negedge aresetn) begin
	if(!aresetn)begin 
	        awready <= 1'b0;
            wready <= 1'b0;
            bresp <= 2'b0;
            bvalid <= 1'b0;
            write_addr <= 32'b0;
            write_data <= 32'b0;
            write_strb <= 4'b0;
            write_state <= IDLE;
	end
	else begin
	case(write_state)
	IDLE:
	begin
	if(awvalid && wvalid)begin 
	        awready <=1'b1;
	        wready <= 1'b1;
	        write_addr <= awaddr;
            write_data <= wdata;
            write_strb <= wstrb;
            write_state <= TRANSFER;
            
	end
	end
	TRANSFER:
	begin
	awready <=1'b1;
	wready <= 1'b1;
	
	case(write_addr)
	                   32'h00000000: if (write_strb[0])begin 
	                                 control_reg[7:0] <= write_data[7:0]; 
	                                 end
                                     else if (write_strb[1])begin 
                                     control_reg[15:8] <= write_data[15:8];
                                     end
                                     else if (write_strb[2]) control_reg[23:16] <= write_data[23:16];
                                     else if (write_strb[3]) control_reg[31:24] <= write_data[31:24];
                        32'h00000004: if (write_strb[0]) status_reg[7:0] <= write_data[7:0];
                                      else if (write_strb[1]) status_reg[15:8] <= write_data[15:8];
                                      else if (write_strb[2]) status_reg[23:16] <= write_data[23:16];
                                      else if (write_strb[3]) status_reg[31:24] <= write_data[31:24];
                        32'h00000008: if (write_strb[0]) data_reg_0[7:0] <= write_data[7:0];
                                      else if (write_strb[1]) data_reg_0[15:8] <= write_data[15:8];
                                      else if (write_strb[2]) data_reg_0[23:16] <= write_data[23:16];
                                      else if (write_strb[3]) data_reg_0[31:24] <= write_data[31:24];
                        32'h0000000C: if (write_strb[0]) data_reg_1[7:0] <= write_data[7:0];
                                      else if (write_strb[1]) data_reg_1[15:8] <= write_data[15:8];
                                      else if (write_strb[2]) data_reg_1[23:16] <= write_data[23:16];
                                      else if (write_strb[3]) data_reg_1[31:24] <= write_data[31:24];
                        default: ; // Handle invalid address
	
	endcase
	                   bresp <= 2'b00;
	                   bvalid <= 1'b1;
	                   write_state <= RESPONSE;
	end
	RESPONSE:
	            begin
                    if (bready) begin
                        bvalid <= 1'b0;
                        write_state <= IDLE;
                    end
                end
	endcase
	
	 end
	
    end

endmodule
