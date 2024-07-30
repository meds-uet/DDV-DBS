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
    logic [3:0]  wstrb;   // Write strobe
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
        forever #(CLK_PERIOD/2) aclk = ~aclk; // Toggle clock every half period
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
        wstrb = 4'b1111; // All bytes enabled
        wvalid = 0;
        bready = 0;

        // Reset sequence
        #(CLK_PERIOD * 5); // Wait for 5 clock cycles
        aresetn = 1;       // De-assert reset
        #(CLK_PERIOD * 2); // Wait for 2 clock cycles

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
            awaddr = addr;
            awvalid = 1;
            wdata = data;
            wvalid = 1;
            bready = 1;
            wait(awready && wready); // Wait until both awready and wready are asserted
            awvalid = 0;
            wvalid = 0;
            wait(bvalid); // Wait until bvalid is asserted
            if (bresp == 2'b00) begin
                $display("Write to address %h successful, data: %h", addr, data);
            end else begin
                $display("Write to address %h failed, response: %b", addr, bresp);
            end
            bready = 0;
        end
    endtask

    // Task for read transaction
    task read_transaction(input [31:0] addr);
        begin
            araddr = addr;
            arvalid = 1;
            rready = 1;
            wait(arready); // Wait until arready is asserted
            arvalid = 0;
            wait(rvalid); // Wait until rvalid is asserted
            if (rresp == 2'b00) begin
                $display("Read from address %h successful, data: %h", addr, rdata);
            end else begin
                $display("Read from address %h failed, response: %b", addr, rresp);
            end
            rready = 0;
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

    // Assertions to check for protocol violations
    assert property (@(posedge aclk) disable iff (!aresetn)
        (awvalid && !awready) |=> $stable(awaddr))
    else $error("AXI4-Lite Protocol Violation: awaddr changed while awvalid high and awready low");

    assert property (@(posedge aclk) disable iff (!aresetn)
        (wvalid && !wready) |=> $stable(wdata))
    else $error("AXI4-Lite Protocol Violation: wdata changed while wvalid high and wready low");

    assert property (@(posedge aclk) disable iff (!aresetn)
        (arvalid && !arready) |=> $stable(araddr))
    else $error("AXI4-Lite Protocol Violation: araddr changed while arvalid high and arready low");

    assert property (@(posedge aclk) disable iff (!aresetn)
        (rvalid && !rready) |=> $stable(rdata))
    else $error("AXI4-Lite Protocol Violation: rdata changed while rvalid high and rready low");
endmodule
