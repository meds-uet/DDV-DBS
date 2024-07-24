module tb_spi_master;

  // Parameters for the testbench
  parameter DATA_WIDTH = 8;
  parameter CLOCK_DIVIDER = 4;
  parameter NUM_SLAVES = 1;

  // Clock and reset signals
  logic clk;
  logic rst_n;

  // SPI Master Interface
  logic [DATA_WIDTH-1:0] tx_data;
  logic [DATA_WIDTH-1:0] rx_data;
  logic start_transaction;
  logic transaction_done;
  logic sclk;
  logic mosi;
  logic miso;
  logic [NUM_SLAVES-1:0] ss_n;

  // Instantiate SPI Master
  spi_master #(
    .DATA_WIDTH(DATA_WIDTH),
    .CLOCK_DIVIDER(CLOCK_DIVIDER),
    .NUM_SLAVES(NUM_SLAVES)
  ) uut (
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
  initial begin
    clk = 0;
    forever #5 clk = ~clk; // 100 MHz clock
  end

  // SPI Slave Model
  logic [DATA_WIDTH-1:0] slave_shift_reg;
  always_ff @(posedge sclk or negedge rst_n) begin
    if (!rst_n) begin
      miso <= 1'b0;
      slave_shift_reg <= 8'hA5; // Initial data to be sent by the slave
    end else if (!ss_n[0]) begin
      miso <= slave_shift_reg[DATA_WIDTH-1];
      slave_shift_reg <= {slave_shift_reg[DATA_WIDTH-2:0], mosi};
    end
  end

  // Testbench components
  class spi_driver;
    virtual task drive_transaction(input logic [DATA_WIDTH-1:0] data);
      tx_data = 8'b0;
      start_transaction = 1;
      tx_data = data;
      @(posedge clk);
      start_transaction = 0;
      @(posedge transaction_done); // Wait for transaction to complete
    endtask
  endclass

  class spi_monitor;
    logic [DATA_WIDTH-1:0] observed_rx_data;
    // Monitor SPI transactions
    virtual task monitor_transaction();
      forever begin
        @(posedge transaction_done);
        observed_rx_data = rx_data;
        $display("Transaction Done: RX Data = %h", observed_rx_data);
      end
    endtask
  endclass

  class spi_scoreboard;
    // Check the results of SPI transactions
    virtual task check(input logic [DATA_WIDTH-1:0] expected_data, input logic [DATA_WIDTH-1:0] observed_data);
      if (expected_data !== observed_data) begin
        $display("Error: Expected %h, Observed %h", expected_data, observed_data);
      end else begin
        $display("Transaction successful: %h", observed_data);
      end
    endtask
  endclass

  // Instantiate the driver, monitor, and scoreboard
  spi_driver drv = new();
  spi_monitor mon = new();
  spi_scoreboard sb = new();

  // Monitor task
  initial begin
    fork
      mon.monitor_transaction();
    join_none
  end

  // Drive transactions and check results
  initial begin
    // Reset sequence
    rst_n = 0;
    #20 rst_n = 1;

    // Basic transactions
    $display("Starting Transaction: TX Data = %h", 8'hA5);
    drv.drive_transaction(8'hA5);
    sb.check(8'hA5, mon.observed_rx_data);

    /*#20;
    $display("Starting Transaction: TX Data = %h", 8'h34);
    @(posedge sclk) drv.drive_transaction(8'h34); // For different data width (8-bit)
    sb.check(8'h34, mon.observed_rx_data*/
    // Multiple slave select operations (NUM_SLAVES = 1, so only one slave)
    $display("Starting Transaction: TX Data = %h", 8'hFF);
    @(posedge sclk)drv.drive_transaction(8'hFF);
    sb.check(8'hFF, mon.observed_rx_data);

    $display("Starting Transaction: TX Data = %h", 8'h00);
    @(posedge sclk)drv.drive_transaction(8'h00);
    sb.check(8'h00, mon.observed_rx_data);

    // Different clock rates (this is controlled by the CLOCK_DIVIDER parameter)
    $display("Starting Transaction: TX Data = %h", 8'hAA);
    @(posedge sclk)drv.drive_transaction(8'hAA);
    sb.check(8'hAA, mon.observed_rx_data);

    $finish;
  end

endmodule

