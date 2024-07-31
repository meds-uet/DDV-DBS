module axi_lite_slave_tb;

  // Parameters
  parameter MEMORY_SIZE = 1024;
  parameter DATA_WIDTH  = 32;
  parameter ADDR_WIDTH  = 32;

  // Clock and reset signals
  logic aclk;
  logic aresetn;

  // AXI Lite signals
  logic [ADDR_WIDTH-1:0] araddr;
  logic arvalid;
  logic arready;
  logic [DATA_WIDTH-1:0] rdata;
  logic [1:0] rresp;
  logic rvalid;
  logic rready;
  logic [ADDR_WIDTH-1:0] awaddr;
  logic awvalid;
  logic awready;
  logic [DATA_WIDTH-1:0] wdata;
  logic [3:0] wstrb;
  logic wvalid;
  logic wready;
  logic [1:0] bresp;
  logic bvalid;
  logic bready;

  // Instantiate the AXI Lite Slave module
  axi_lite_slave #(MEMORY_SIZE, DATA_WIDTH, ADDR_WIDTH) dut (
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

  initial begin
    // Initialize signals
    aclk = 1;
    aresetn = 0;

    //READ signals
    araddr = 0;
    arvalid = 0;
    rready = 0;
    awaddr = 0;
    awvalid = 0;
    wdata = 32'h0000_0004;
    wstrb = 0;
    wvalid = 0;
    bready = 0;
    #10;

    aresetn = 1;

    //READ signals
    arvalid = 1;
    araddr  = 32'h0000_0000;

    //WRITE signals
    awvalid = 1;
    awaddr  = 32'h0000_0004;

    #20;

    //READ signals
    arvalid = 0;
    rready  =1;

    //WRITE signals
    wvalid = 1;
    wstrb  = 4'b0001;

    #40;

    //READ signal
    rready  = 0;

    //WRITE signals
    awvalid = 0;
    wvalid  = 0;
    bready  = 1;

    #40;

    bready = 0;

    #20;

    $finish;
  end

    initial begin
        $dumpfile("axi.vcd");
        $dumpvars(0, axi_lite_slave_tb);
    end

endmodule