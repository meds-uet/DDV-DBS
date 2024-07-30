module tb_spi_master;

  // Parameters
  localparam DATA_WIDTH = 8;      // Data width for SPI transactions (8 bits)
  localparam CLOCK_DIVIDER = 8;   // Clock divider for SPI clock rate
  localparam CLK_PERIOD = 10;     // Clock period in ns (for a 100 MHz system clock)

  // Testbench signals
  logic clk;                     // System clock signal
  logic rst_n;                   // Active-low reset signal
  logic start_transaction;      // Signal to start SPI transaction
  logic [DATA_WIDTH-1:0] tx_data; // Data to be transmitted
  logic [DATA_WIDTH-1:0] rx_data; // Data received from SPI
  logic transaction_done;        // Flag to indicate transaction completion
  logic sclk;                    // SPI clock signal
  logic mosi;                    // Master Out Slave In
  logic miso;                    // Master In Slave Out
  logic ss_n;                    // Slave Select (active low)

  // Instantiate the Unit Under Test (UUT)
  spi_master #(
    .DATA_WIDTH(DATA_WIDTH),
    .CLOCK_DIVIDER(CLOCK_DIVIDER)
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
    // Generate a clock signal with period defined by CLK_PERIOD
    forever #(CLK_PERIOD / 2) clk = ~clk;
  end

  // Test stimulus
  initial begin
    // Initialize signals
    rst_n = 0;                   // Assert reset
    start_transaction = 0;      // Deassert start transaction
    tx_data = 0;                // Initialize transmit data
    miso = 0;                   // Default value for MISO
    #(CLK_PERIOD * 5);          // Wait for 5 clock periods
    rst_n = 1;                 // Release reset
    #(CLK_PERIOD * 2);         // Wait for 2 clock periods

    // Test case 1: Write data to SPI Master and read it back
    perform_transaction(8'hA5, 8'hA5);  // Expected result: rx_data should be 8'hA5

    // Test case 2: Back-to-back transactions
    perform_transaction(8'hFF, 8'hFF);  // Expected result: rx_data should be 8'hFF
    perform_transaction(8'h55, 8'h55);  // Expected result: rx_data should be 8'h55

    // Test case 3: Error condition (changing slave select mid-transaction)
    start_transaction = 1;   // Start a new transaction
    tx_data = 8'h3C;         // Data to transmit
    #(CLK_PERIOD * 2);       // Wait a bit to simulate mid-transaction error
    ss_n = 1;               // Deactivate slave select (simulate error)
    #(CLK_PERIOD * 5);       // Wait to allow transaction to complete
    start_transaction = 0;  // End transaction

    // End simulation
    #(CLK_PERIOD * 20);     // Wait for additional time
    $finish;                // Terminate simulation
  end

  // Task to perform a SPI transaction
  task perform_transaction(input [DATA_WIDTH-1:0] write_data, input [DATA_WIDTH-1:0] expected_data);
    begin
      start_transaction = 1; // Signal to start the transaction
      tx_data = write_data; // Set data to transmit
      #(CLK_PERIOD * 2);     // Wait for a couple of clock periods
      start_transaction = 0; // End the start signal
      wait(transaction_done); // Wait until the transaction is complete
      if (rx_data == expected_data) begin
        // Check if received data matches expected data
        $display("Transaction successful: Write Data = %h, Received Data = %h", write_data, rx_data);
      end else begin
        // Report error if received data does not match expected data
        $display("Transaction failed: Write Data = %h, Expected Data = %h, Received Data = %h", write_data, expected_data, rx_data);
      end
    end
  endtask

  // Monitor to display SPI transactions
  initial begin
    $monitor("Time: %0t | clk: %b | rst_n: %b | start_transaction: %b | tx_data: %h | rx_data: %h | transaction_done: %b | sclk: %b | mosi: %b | miso: %b | ss_n: %b", 
             $time, clk, rst_n, start_transaction, tx_data, rx_data, transaction_done, sclk, mosi, miso, ss_n);
  end

  // Check for SPI protocol violations
  assert property (@(posedge clk) disable iff (!rst_n)
    (ss_n == 0) |=> $stable(mosi))
  else $error("SPI Protocol Violation: mosi changed while ss_n is active");

  assert property (@(posedge clk) disable iff (!rst_n)
    (sclk == 0) |=> $stable(mosi))
  else $error("SPI Protocol Violation: mosi changed while sclk is low");

endmodule
