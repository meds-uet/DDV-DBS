

module tb_axi_lite_slave;

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
    logic        wvalid;  // Write valid
    logic        wready;  // Write ready

    // Write response channel
    logic [1:0]  bresp;   // Write response
    logic        bvalid;  // Write response valid
    logic        bready;  // Write response ready

    // Instantiate the Unit Under Test (UUT)
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
        aresetn = 0;
        araddr = 0;
        arvalid = 0;
        rready = 0;
        awaddr = 0;
        awvalid = 0;
        wdata = 0;
        wvalid = 0;
        bready = 0;

        // Reset the DUT
        #(CLK_PERIOD * 2);
        aresetn = 1;

        // Test case 1: Write to control register (address 0x0000)
        write_transaction(32'h0000, 32'hA5A5A5A5);

        // Test case 2: Read from control register (address 0x0000)
        read_transaction(32'h0000);

        // Test case 3: Write to data register 0 (address 0x0008)
        write_transaction(32'h0008, 32'h12345678);

        // Test case 4: Read from data register 0 (address 0x0008)
        read_transaction(32'h0008);

        // Test case 5: Write to invalid address
        write_transaction(32'h1000, 32'hDEADBEEF);

        // Test case 6: Read from invalid address
        read_transaction(32'h1000);

        // End simulation
        #(CLK_PERIOD * 10);
        $finish;
    end

    // Task for write transaction
    task write_transaction(input [31:0] addr, input [31:0] data);
        begin
            @(posedge aclk);
            awaddr <= addr;
            awvalid <= 1;
            wdata <= data;
            wvalid <= 1;
            bready <= 1;
            @(posedge aclk);
            while (!awready || !wready) begin
                @(posedge aclk);
            end
            awvalid <= 0;
            wvalid <= 0;
            @(posedge aclk);
            while (!bvalid) begin
                @(posedge aclk);
            end
            bready <= 1;
            @(posedge aclk);
            bready <= 0;
        end
    endtask

    // Task for read transaction
    task read_transaction(input [31:0] addr);
        begin
            @(posedge aclk);
            araddr <= addr;
            arvalid <= 1;
            rready <= 1;
            @(posedge aclk);
            while (!arready) begin
                @(posedge aclk);
            end
            arvalid <= 0;
            @(posedge aclk);
            while (!rvalid) begin
                @(posedge aclk);
            end
            rready <= 0;
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
    assert property (@(posedge aclk) disable iff (!aresetn)
        (awvalid && !awready) |=> $stable(awaddr))
    else $error("AXI4-Lite Protocol Violation: awaddr changed while awvalid high and awready low");
endmodule
