module fifo_tb;

  parameter FIFO_WIDTH = 128;
  parameter DATA_WIDTH = 8;

  // Testbench signals
  logic clk;
  logic rst_n;
  logic [7:0] d_i;
  logic wr_en;
  logic rd_en;
  logic [7:0] d_o;
  logic full;
  logic empty;

  // Instantiate the FIFO module
  fifo #(FIFO_WIDTH, DATA_WIDTH) dut (
    .clk(clk),
    .rst_n(rst_n),
    .d_i(d_i),
    .wr_en(wr_en),
    .rd_en(rd_en),
    .d_o(d_o),
    .full(full),
    .empty(empty)
  );

  // Clock generation
  always #5 clk = ~clk;

  // Test sequence
  initial begin
    // Initialize signals
    clk = 0;
    rst_n = 0;
    d_i = 0;
    wr_en = 0;
    rd_en = 0;

    #10 rst_n = 1;
    d_i = 8'hA5;
    wr_en = 1;
    rd_en =1;
    #10000 $finish;
  end

    initial begin
        $dumpfile("fifo.vcd");
        $dumpvars(0, fifo_tb);
    end

endmodule