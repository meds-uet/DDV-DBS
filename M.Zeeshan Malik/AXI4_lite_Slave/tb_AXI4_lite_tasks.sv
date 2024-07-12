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

    // Instantiate DUT
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

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Reset generation
    initial begin
        reset = 1;
        #20 reset = 0;
    end

    // AXI4-Lite write task
    task axi_write(input [31:0] addr, input [31:0] data, input [3:0] strb);
        begin
            @(posedge clk);
            awaddr = addr;
            awprot = 3'b000;
            awvalid = 1;
            @(posedge clk);
            while (!awready) @(posedge clk);
            awvalid = 0;

            @(posedge clk);
            wdata = data;
            wstrb = strb;
            wvalid = 1;
            @(posedge clk);
            while (!wready) @(posedge clk);
            wvalid = 0;

            @(posedge clk);
            bready = 1;
            @(posedge clk);
            while (!bvalid) @(posedge clk);
            bready = 0;
        end
    endtask

    // AXI4-Lite read task
    task axi_read(input [31:0] addr, output [31:0] data);
        begin
            @(posedge clk);
            araddr = addr;
            arprot = 3'b000;
            arvalid = 1;

            @(posedge clk);
            rready = 1;
            @(posedge clk);
            while (!rvalid) @(posedge clk);
            data = rdata;
            rready = 0;
        end
    endtask

    // Test cases
    initial begin
        // Initialize signals
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
        axi_write(0, 32'h12345678, 4'b1111);

        // Case 2: Read transaction
        logic [31:0] read_data;
        axi_read(0, read_data);

        // Case 3: Write transaction to invalid address
        axi_write(50, 32'h87654321, 4'b1111);

        // Case 4: Read transaction from invalid address
        axi_read(50, read_data);

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
