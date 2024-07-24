module tb_AXI4_lite;

    
    logic clk;
    logic reset;
    
    
    logic [31:0] awaddr;
    logic [2:0] awprot;
    logic awvalid;
    logic [31:0] wdata;
    logic [3:0] wstrb;
    logic wvalid;
    logic [31:0] araddr;
    logic [2:0] arprot;
    logic arvalid;
    logic rready;
    logic bready;

    
    logic awready;
    logic wready;
    logic [1:0] bresp;
    logic bvalid;
    logic [31:0] rdata;
    logic [1:0] rresp;
    logic rvalid;
    logic arready;

    AXI4_Lite_Slave_Address dut (
        .clk(clk),
        .reset(reset),
        .awaddr(awaddr),
        .awprot(awprot),
        .awvalid(awvalid),
        .awready(awready),
        .wdata(wdata),
        .wstrb(wstrb),
        .wvalid(wvalid),
        .wready(wready),
        .bresp(bresp),
        .bvalid(bvalid),
        .bready(bready),
        .araddr(araddr),
        .arprot(arprot),
        .arvalid(arvalid),
        .arready(arready),
        .rdata(rdata),
        .rresp(rresp),
        .rvalid(rvalid),
        .rready(rready)
    );

    
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

  
    initial begin
        reset = 1;
        #20 reset = 0;
    end

    // Test cases
    initial begin
        
        awaddr = 0;
        awprot = 0;
        awvalid = 0;
        wdata = 0;
        wstrb = 0;
        wvalid = 0;
        araddr = 0;
        arprot = 0;
        arvalid = 0;
        rready = 0;
        bready = 0;

        #30; 

        // Case 1: Write transaction
        @(posedge clk);
        awaddr = 0;
        awprot = 3'b000;
        awvalid = 1;
        @(posedge clk);
        while (!awready) @(posedge clk);
        awvalid = 0;

        @(posedge clk);
        wdata = 32'h12345678;
        wstrb = 4'b1111;
        wvalid = 1;
        @(posedge clk);
        while (!wready) @(posedge clk);
        wvalid = 0;

        @(posedge clk);
        bready = 1;
        @(posedge clk);
        while (!bvalid) @(posedge clk);
        bready = 0;

        // Scenario 2: Read transaction
        
        araddr = 0;
        arprot = 3'b000;
        arvalid = 1;
        
        @(posedge clk);
        rready = 1;
        @(posedge clk);
        while (!rvalid) @(posedge clk);
        rready = 0;

        // Additional scenarios can be added here

        // Scenario 3: Write transaction to invalid address
        @(posedge clk);
        awaddr = 50;
        awprot = 3'b000;
        awvalid = 1;
        @(posedge clk);
        while (!awready) @(posedge clk);
        awvalid = 0;

        @(posedge clk);
        wdata = 32'h12345678;
        wstrb = 4'b1111;
        wvalid = 1;
        @(posedge clk);
        while (!wready) @(posedge clk);
        wvalid = 0;

        @(posedge clk);
        bready = 1;
        @(posedge clk);
        while (!bvalid) @(posedge clk);
        bready = 0;

        // Scenario 4: Read transaction from invalid address
        @(posedge clk);
        araddr = 50;
        arprot = 3'b000;
        arvalid = 1;
        

        @(posedge clk);
        rready = 1;
        @(posedge clk);
        while (!rvalid) @(posedge clk);
        rready = 0;

        // Finish simulation
        $finish;
    end

    // Monitor state transitions and outputs
    always @(posedge clk) begin
        $display("Time %0t: Write State - %0s, Read State - %0s", $time, dut.write_state.name(), dut.read_state.name());
        if (rvalid) begin
            $display("Time %0t: Read Data - %h, Read Response - %b", $time, rdata, rresp);
        end
        if (bvalid) begin
            $display("Time %0t: Write Response - %b", $time, bresp);
        end
    end

endmodule
