module spi_master_tb();

  // Parameters
  parameter CLK_PERIOD = 10; // Clock period in ns

  // Signals
  logic clk;
  logic rst_n;
  logic start_transaction;
  logic [7:0] tx_data;
  logic [7:0] rx_data;
  logic transaction_done;
  logic sclk;
  logic mosi;
  logic miso;
  logic ss_n;

  // Instantiate the spi_master module
  spi_master dut (
    .clk(clk),
    .rst_n(rst_n),
    .start_transaction(start_transaction),
    .tx_data(tx_data),
    .rx_data(rx_data),
    .transaction_done(transaction_done),
    .sclk(sclk),
    .mosi(mosi),
    .miso(miso),
    .ss_n(ss_n)
  );

  // Clock generation
  always #CLK_PERIOD clk = ~clk;

  // Reset initialization
  initial begin
    clk = 0;
    rst_n = 0;
    start_transaction = 0;
    tx_data = 8'b0;
    miso = 1'b1;

    // Reset release after a short delay
    #10;
    rst_n = 1;

    // Start a transaction after another short delay
    #10;
    start_transaction = 1;
    tx_data = 8'b11001010; // Example data to transmit

    // Simulation for one complete transaction
    #10;
    start_transaction = 0;
    #20;
    miso = 1'b1; // Simulate MISO line response

    // End of simulation
    #1000;
    $stop;
  end

  // Monitor for displaying relevant signals
  always @(posedge clk) begin
    $display("[Time %0t] State: %0d, tx_data: %h, rx_data: %h, transaction_done: %b, sclk: %b",
             $time, dut.current_state, dut.tx_data, dut.rx_data, dut.transaction_done, dut.sclk);
  end

endmodule
