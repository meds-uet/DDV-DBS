module tb_spi_master;

  parameter DATA_WIDTH = 8;
  parameter CLOCK_DIVIDER = 4;
  parameter NUM_SLAVES = 4;

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
  logic [$clog2(NUM_SLAVES)-1:0] slave_select;

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
    .ss_n(ss_n),
    .slave_select(slave_select)
  );

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk; // 100 MHz clock
  end

  // SPI Slave Model
  logic [DATA_WIDTH-1:0] slave_shift_reg[NUM_SLAVES];
  always_ff @(posedge sclk or negedge rst_n) begin
    if (!rst_n) begin
      for (int i = 0; i < NUM_SLAVES; i++) begin
        slave_shift_reg[i] <= 8'hA5 + i; // Initial data for each slave
      end
      miso <= 1'b0;
    end else begin
      for (int i = 0; i < NUM_SLAVES; i++) begin
        if (!ss_n[i]) begin
          miso <= slave_shift_reg[i][DATA_WIDTH-1];
          slave_shift_reg[i] <= {slave_shift_reg[i][DATA_WIDTH-2:0], mosi};
        end
      end
    end
  end

  // Testbench components
  class spi_driver;
    virtual task drive_transaction(input logic [DATA_WIDTH-1:0] data, input logic [$clog2(NUM_SLAVES)-1:0] slave);
      tx_data = '0;
      start_transaction = 1;
      tx_data = data;
      slave_select = slave;
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
    $display("Starting Transaction: TX Data = %h, Slave = 0", 8'hA5);
    drv.drive_transaction(8'hA5, 0);
    sb.check(8'hA5, mon.observed_rx_data);

    #20;
    $display("Starting Transaction: TX Data = %h, Slave = 1", 8'h34);
    drv.drive_transaction(8'h34, 1);
    sb.check(8'hA6, mon.observed_rx_data); // Expect A6 from slave 1

    // Multiple slave select operations
    $display("Starting Transaction: TX Data = %h, Slave = 2", 8'hFF);
    drv.drive_transaction(8'hFF, 2);
    sb.check(8'hA7, mon.observed_rx_data); // Expect A7 from slave 2

    $display("Starting Transaction: TX Data = %h, Slave = 3", 8'h00);
    drv.drive_transaction(8'h00, 3);
    sb.check(8'hA8, mon.observed_rx_data); // Expect A8 from slave 3

    // Different clock rates (this is controlled by the CLOCK_DIVIDER parameter)
    $display("Starting Transaction: TX Data = %h, Slave = 0", 8'hAA);
    drv.drive_transaction(8'hAA, 0);
    sb.check(8'h52, mon.observed_rx_data); // Expect 52 (shifted A5) from slave 0

    $finish;
  end

endmodule