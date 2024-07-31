`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/11/2024 11:50:01 AM
// Design Name: 
// Module Name: AXI4Slave_tb
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

module tb_axi4_lite_slave;
    logic ACLK;
    logic ARESETn;
    logic [31:0]  AWADDR;
    logic AWVALID;
    logic AWREADY;
    logic [31:0]  WDATA;
    logic [3:0]   WSTRB;
    logic WVALID;
    logic WREADY;
    logic [1:0]  BRESP;
    logic BVALID;
    logic BREADY;
    logic [31:0]  ARADDR;
    logic ARVALID;
    logic ARREADY;
    logic [31:0] RDATA;
    logic [1:0]  RRESP;
    logic RVALID;
    logic  RREADY;

    axi4LiteSlave uut (.ACLK(ACLK), .ARESETn(ARESETn), .AWADDR(AWADDR), .AWVALID(AWVALID),.AWREADY(AWREADY), .WDATA(WDATA),.WSTRB(WSTRB),
        .WVALID(WVALID), .WREADY(WREADY), .BRESP(BRESP), .BVALID(BVALID), .BREADY(BREADY), .ARADDR(ARADDR),.ARVALID(ARVALID), .ARREADY(ARREADY),
        .RDATA(RDATA), .RRESP(RRESP), .RVALID(RVALID), .RREADY(RREADY) );

    initial begin
        // Initialize signals
        ACLK = 0;
        ARESETn = 0;
        AWADDR = 0;
        AWVALID = 0;
        WDATA = 0;
        WSTRB = 4'b1111;
        WVALID = 0;
        BREADY = 0;
        ARADDR = 0;
        ARVALID = 0;
        RREADY = 0;
        RDATA = 0;

        // OFF the Reset 
        #10 ARESETn = 1;

        // Write transaction
        #10 AWADDR = 32'h00000004; AWVALID = 1;
      #10 WDATA = 32'hDEADBEEF; WVALID = 1;
        #10 AWVALID = 0; WVALID = 0;
      #10 BREADY = 1;
      #10 BREADY = 0;

        // Read transaction
       #10 ARADDR = 32'h00000004; ARVALID = 1;
      #10 ARVALID = 0;
      #10 RREADY = 1;
       #10 RREADY = 0;

        // Finish simulation
        //#100 $finish;
    end

    always #5 ACLK = ~ACLK;

endmodule

