`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/11/2024 11:45:23 AM
// Design Name: 
// Module Name: AXI4Slave
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

module axi4LiteSlave (
    input ACLK,
    input ARESETn,
    input [31:0] AWADDR,
    input AWVALID,
    output logic AWREADY,
    input [31:0] WDATA,
    input [3:0]  WSTRB,
    input WVALID,   ////
    output logic WREADY, ////
    output logic[1:0] BRESP,
    output logic BVALID,
    input BREADY,
    input [31:0] ARADDR,
    input ARVALID,
    output logic ARREADY,
    output logic[31:0] RDATA,
    output logic[1:0] RRESP,
    output logic RVALID,
    input RREADY
);
                             
    logic [31:0] regfile [1024:0];  
                                        //  Set of memory-mapped registers
    logic [1:0]  bresp_reg;
    logic [31:0] rdata_reg;
    logic [1:0]  rresp_reg;
    logic awready_reg, wready_reg, bvalid_reg, arready_reg, rvalid_reg;

    assign AWREADY = awready_reg;
    assign WREADY = wready_reg;
    assign BRESP = bresp_reg;
    assign BVALID = bvalid_reg;
    assign ARREADY = arready_reg;
    assign RDATA = rdata_reg;
    assign RRESP = rresp_reg;
    assign RVALID = rvalid_reg;

    always @(posedge ACLK) begin
        if (!ARESETn) begin
            awready_reg <= 1'b0;
            wready_reg <= 1'b0;
            bvalid_reg <= 1'b0;
            arready_reg <= 1'b0;
            rvalid_reg <= 1'b0;
            bresp_reg <= 2'b00;
            rresp_reg <= 2'b00;
            rdata_reg <= 32'd0;
        end 
        
        else begin
                                              /////////WRITE CHANNEL////////////////
               // Write Address Channel
            if (AWVALID && !awready_reg) begin
                awready_reg <= 1'b1;
            end else if (WVALID && !wready_reg) begin
                wready_reg <= 1'b1;
            end else begin
                awready_reg <= 1'b0;
                wready_reg <= 1'b0;
            end
            
             // Write Data Channel
            if (WVALID && awready_reg && WREADY) begin
                regfile[AWADDR] <= WDATA;
                bvalid_reg <= 1'b1;
                bresp_reg <= 2'b00;  // OKAY response
            end else if (bvalid_reg && BREADY) begin
                bvalid_reg <= 1'b0;
            end
                                                /////////READ CHANNEL/////////////
            // Read Address Channel
            if (ARVALID && !arready_reg) begin
                arready_reg <= 1'b1;
            end else begin
                arready_reg <= 1'b0;
            end
            
            // Read Data Channel
            if (arready_reg && ARVALID) begin
                RDATA <= regfile[ARADDR];
                rvalid_reg <= 1'b1;
                rresp_reg <= 2'b00;  // OKAY response
            end else if (RVALID && RREADY) begin
                rvalid_reg <= 1'b0;
            end
        end
    end
endmodule
