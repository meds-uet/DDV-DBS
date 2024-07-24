module tb_spi_master;

  // Testbench signals
  logic clk;
  logic reset;
  logic start_transaction;
  logic [7:0] tx_data;
  logic [7:0] rx_data;
  logic transaction_done;
  logic sclk;
  logic mosi;
  logic miso;
  logic ss_n;

  // Instantiate the SPI master module
  spi_master uut (
    .clk(clk),
    .reset(reset),
    .start_transaction(start_transaction),
    .tx_data(tx_data),
    .rx_data(rx_data),
    .transaction_done(transaction_done),
    .sclk(sclk),
    .mosi(mosi),
    .miso(miso),
    .ss(ss)
  );

  // Generate clock
  initial begin
    clk = 0;
    forever #20 clk = ~clk; // 100MHz clock (10ns period)
  end


  // Reset sequence
  initial begin
    reset = 1;
    #50
    reset = 0;
  end


  initial begin
    start_transaction = 1'b0;
    #10
    start_transaction = 1'b1;
    @(posedge clk);
    tx_data = 8'b1111_1001;
    @(posedge clk);
    tx_data = 8'b1000_0101;
  end


  

endmodule

