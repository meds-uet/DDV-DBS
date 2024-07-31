`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/05/2024 12:54:09 PM
// Design Name: 
// Module Name: AXI4_lite
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


module AXI4_lite
//# (paramter addr=32, paramter data=32)
(
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
logic [31:0] data_reg_2;   // Data register 2 for general-purpose use
logic [31:0] data_reg_3;   // Data register 3 for general-purpose use


// Internal signals
logic [31:0] read_addr;   // Latched read address
logic [31:0] write_addr;  // Latched write address
logic [31:0] write_data;  // Latched write data
// FSM states for read and write operations
typedef enum logic [1:0] {IDLE, TRANSFER, RESPONSE} state_t;
state_t read_state,read_state_next, write_state,write_state_next;

// Read operation logic here
/*
Logic:
* Reset all read-related signals and state
* In read state:
    at IDLE state,If arvalid then Latch the read address and transition to TRANSFER state,
    at TRANSFER state, Select the appropriate register based on the address  or update response based on invalid address
    at RESPONSE state, Complete the transfer and return to IDLE state
*/
always_ff @(posedge aclk) begin
// TODO: ADD READ LOGIC HERE!!!
if(aresetn)
begin
rdata<=0;
rresp<=0;
rvalid<=0;
arready<=1;
read_state<=IDLE;

end
else
begin
read_state<=read_state_next;

end
end
always_comb
begin
//Read Channel
case(read_state)
IDLE:
begin if(arvalid && arready) begin read_addr=araddr;read_state_next=TRANSFER; end end
TRANSFER:begin
if (rready)
begin
rresp=2'b00;arready=0; 
case (read_addr)
32'h00000000: rdata=data_reg_0; 
32'h00000004: rdata=data_reg_1; 
32'h00000008: rdata=data_reg_2; 
32'h0000000c: rdata=data_reg_3;
endcase
read_state_next=RESPONSE;
end
else begin read_state_next=IDLE;rvalid=0;rresp=10; 
    $display("invalid adress read adress"); 
    end 
    end   
RESPONSE:begin rvalid=1;arready=0;read_state_next=IDLE; end 
default: read_state_next = IDLE;
endcase
end







// Write operation logic
/* 
Logic:
* If reset, Reset all write-related signals and state
* If write state, and at IDLE state, Latch write address and data, transition to TRANSFER state
* If write state, and at TRABSFER state, Perform the write operation based on the address
* If write state, and at RESPONSE state, Complete the transfer and return to IDLE state
*/
always_ff @(posedge aclk ) begin
// TODO: ADD WRITE LOGIC HERE!!!
if(aresetn)
begin
awready<=1;
bresp<=0;
bvalid<=0;
wready<=1;
bvalid<=0;
write_state<=IDLE;
end
else 

begin
write_state<=write_state_next;
end
end
always_comb
begin

//write channel
case(write_state)
IDLE:
begin if(awvalid && awready) begin write_addr=awaddr; wready=1; write_state_next=TRANSFER; end end
TRANSFER: begin
if(wvalid && bready && wready)
begin
awready=0;
case(write_addr)
32'h00000000: data_reg_0=wdata;  
32'h00000004: data_reg_1=wdata; 
32'h00000008: data_reg_2=wdata; 
32'h0000000c: data_reg_3=wdata;

endcase
//if (write_addr==32'h00000000)
//data_reg_0=wdata; 
//else if (write_addr==32'h000000044)
//data_reg_1=wdata;
//else if (write_addr==32'h00000008)
//data_reg_2=wdata;
//else if (write_addr==32'h0000000c)
//data_reg_3=wdata;


 write_state_next=RESPONSE;
end
else begin bresp=10;wready=0;awready=1;$display("invalid adress write adress"); write_state_next=IDLE; end
end
RESPONSE: begin bresp=00;bvalid=1;wready=1;write_state_next=IDLE; end 
default: write_state_next = IDLE;
endcase
end




//end
//always_comb begin
//case(write_state)
//IDLE:if(awvalid&&awready) begin write_state=TRANSFER; end
//TRANSFER:if(wvalid && bready && wready &&(write_addr==32'h00000000))begin write_state=RESPONSE; end else begin write_state=IDLE; end
//TRANSFER:if(wvalid && bready && wready && write_addr==32'h00000004)begin  write_state=RESPONSE; end else begin write_state=IDLE; end
//TRANSFER:if(wvalid && bready && wready && write_addr==32'h00000008)begin  write_state=RESPONSE; end else begin write_state=IDLE; end
//TRANSFER:if(wvalid && bready && wready && write_addr==32'h0000000c)begin write_state=RESPONSE; end else begin write_state=IDLE; end
//RESPONSE: begin write_state=IDLE; end 
//endcase
//end

//function transfer()




endmodule


