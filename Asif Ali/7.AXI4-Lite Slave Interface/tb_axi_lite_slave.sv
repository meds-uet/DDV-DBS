module tb_axi_lite_slave;

    // Clock and reset signals
    logic aclk;
    logic aresetn;

    // AXI signals
    logic [31:0] araddr;
    logic arvalid;
    logic arready;
    logic [31:0] rdata;
    logic [1:0] rresp;
    logic rvalid;
    logic rready;
    logic [31:0] awaddr;
    logic awvalid;
    logic awready;
    logic [31:0] wdata;
    logic [3:0] wstrb;
    logic wvalid;
    logic wready;
    logic [1:0] bresp;
    logic bvalid;
    logic bready;

    // DUT instance
    axi_lite_slave uut (
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
    always #5 aclk = ~aclk;

    // Test procedure
    initial begin
        // Initialize signals
        aclk = 0;
        aresetn = 0;
        araddr = 0;
        arvalid = 0;
        rready = 0;
        awaddr = 0;
        awvalid = 0;
        wdata = 0;
        wstrb = 0;
        wvalid = 0;
        bready = 0;

        // Apply reset
        #10;
        aresetn = 1;

        // Test write operation
        #10;
        awaddr = 32'h0000_0000; // Write to control register
        awvalid = 1;
        @(posedge aclk);
        while (!awready) @(posedge aclk);
        awvalid = 0;

        wdata = 32'hABCD_1234;
        wstrb = 4'b1111;
        wvalid = 1;
        @(posedge aclk);
        while (!wready) @(posedge aclk);
        wvalid = 0;

        bready = 1;
        @(posedge aclk);
        while (!bvalid) @(posedge aclk);
        bready = 0;

        // Test read operation
        #10;
        araddr = 32'h0000_0000; // Read from control register
        arvalid = 1;
        @(posedge aclk);
        while (!arready) @(posedge aclk);
        arvalid = 0;

        rready = 1;
        @(posedge aclk);
        while (!rvalid) @(posedge aclk);
        rready = 0;

        // Display read data
        $display("Read data: 0x%08X", rdata);

        // End of test
        #20;
        $stop;
    end

endmodule
