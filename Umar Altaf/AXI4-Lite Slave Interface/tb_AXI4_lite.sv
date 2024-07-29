`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/05/2024 12:54:34 PM
// Design Name: 
// Module Name: tb_AXI4_lite
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


module tb_AXI4_lite;

    // Clock period definition
    localparam CLK_PERIOD = 10; // 10 ns clock period (100 MHz)

    // AXI4-Lite interface signals
    logic        aclk;    // Clock signal
    logic        aresetn; // Active-low reset signal

    // Read address channel
    logic [31:0] araddr;  // Read address
    logic        arvalid; // Read address valid
    logic        arready; // Read address ready

    // Read data channel
    logic [31:0] rdata;   // Read data
    logic [1:0]  rresp;   // Read response
    logic        rvalid;  // Read valid
    logic        rready;  // Read ready

    // Write address channel
    logic [31:0] awaddr;  // Write address
    logic        awvalid; // Write address valid
    logic        awready; // Write address ready

    // Write data channel
    logic [31:0] wdata;   // Write data
    logic [3:0]  wstrb;   // Write strobe
    logic        wvalid;  // Write valid
    logic        wready;  // Write ready

    // Write response channel
    logic [1:0]  bresp;   // Write response
    logic        bvalid;  // Write response valid
    logic        bready;  // Write response ready

    // Instantiate the Unit Under Test (UUT)
    AXI4_lite uut (
        .aclk(aclk),
        .aresetn(aresetn),
        .araddr(araddr),
        .arvalid(arvalid),
        .arready(arready),
        .rdata(rdata),
        .rresp(rresp),
        .rvalid(rvalid),
        .rready(rready),
        .awaddr(awaddr),
        .awvalid(awvalid),
        .awready(awready),
        .wdata(wdata),
        .wstrb(wstrb),
        .wvalid(wvalid),
        .wready(wready),
        .bresp(bresp),
        .bvalid(bvalid),
        .bready(bready)
    );

    // Clock generation
    initial begin
        aclk = 0;
        forever #(CLK_PERIOD/2) aclk = ~aclk;
    end

    // Test stimulus
    initial begin
        // Initialize all signals
        aresetn = 1;
        araddr = 0;
        arvalid = 0;
        rready = 0;
        awaddr = 0;
        awvalid = 0;
        wdata = 0;
        //wstrb = 4'b1111;
        wvalid = 0;
        bready = 0;

        // Reset sequence
//        #(CLK_PERIOD * 5);
//        aresetn = 1;
//        #(CLK_PERIOD * 2);
  
    @(posedge aclk);
    aresetn=1;
      @(posedge aclk);
      
      aresetn = 0;
      @(posedge aclk);
      awvalid=1;
       @(posedge aclk);
        // Test case 1: Write to control register (address 0x0000)
        // TODO: write_transaction(32'h0000, 32'hA5A5A5A5);
       bready=1; wvalid=1;
        write_transaction(32'h00000000, 32'hA5A5A5A5);
        @(posedge aclk);
     
        bready=0; awvalid=0;wvalid=0;
        // Test case 2: Read from control register (address 0x0000)
        // TODO: read_transaction(32'h0000);
          @(posedge aclk);
          arvalid=1;
           @(posedge aclk);
        rready=1;

//second signal
  @(posedge aclk);
    awvalid=1;
     @(posedge aclk);
      // Test case 1: Write to control register (address 0x0000)
      // TODO: write_transaction(32'h0000, 32'hA5A5A5A5);
     bready=1; wvalid=1;
      write_transaction(32'h00000004, 32'hf0f00f0f);
      @(posedge aclk);
   
      bready=0; awvalid=0;wvalid=0;
      // Test case 2: Read from control register (address 0x0000)
      // TODO: read_transaction(32'h0000);
        @(posedge aclk);
        arvalid=1;
         @(posedge aclk);
      rready=1;






       read_transaction(32'h00000000);
       @(posedge aclk);
      arvalid=0;rready=0;
        // Test case 3: Write to data register 0 (address 0x0008)
        // TODO: write_transaction(32'h0008, 32'h12345678);

        // Test case 4: Read from data register 0 (address 0x0008)
        // TODO: read_transaction(32'h0008);

        // Test case 5: Write to invalid address
        // TODO: write_transaction(32'h1000, 32'hDEADBEEF);

        // Test case 6: Read from invalid address
        // TODO: read_transaction(32'h1000);

        // End simulation
//        #(CLK_PERIOD * 10);
repeat(10) @(posedge aclk);
        $finish;
    end

    // Task for write transaction
    task write_transaction(input [31:0] addr, input [31:0] data);
        begin
		// TODO: Define this task to perform a write transaction
		awaddr=addr;
		wdata=data;
//		if(wvalid && bready && wready && awaddr==32'h0000)
//		 data_reg_0<=wdata;
        end
    endtask

    // Task for read transaction
    task read_transaction(input [31:0] addr);
        begin
	// TODO: Define this task to perform a read transaction 
	araddr<=addr;
        end
    endtask

    // Monitor process to display transactions
    initial begin
        forever begin
            @(posedge aclk);
            if (awvalid && awready)
                $display("Write Address: %h", awaddr);
            if (wvalid && wready)
                $display("Write Data: %h", wdata);
            if (bvalid && bready)
                $display("Write Response: %h", bresp);
            if (arvalid && arready)
                $display("Read Address: %h", araddr);
            if (rvalid && rready)
                $display("Read Data: %h, Response: %h", rdata, rresp);
        end
    end

    // Assertion to check for protocol violations
//    assert property (@(posedge aclk) disable iff (!aresetn)
//        (awvalid && !awready) |=> $stable(awaddr))
//    else $error("AXI4-Lite Protocol Violation: awaddr changed while awvalid high and awready low");
    // TODO: Add more assertions based on your understanding

endmodule
