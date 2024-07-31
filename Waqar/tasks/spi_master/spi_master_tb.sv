module spi_master_tb;

  // Testbench signals
  logic       clk;
  logic       rst_n;
  logic       start_transaction; 
  logic [7:0] tx_data;
  logic [7:0] rx_data;          
  logic       transaction_done;
  logic       sclk;  
  logic       mosi;             
  logic       miso;             
  logic       ss_n;

  // Expected values
  logic [7:0] expected_rx_data;

  spi_master dut(
    .clk(clk), .rst_n(rst_n), .start_transaction(start_transaction),
    .tx_data(tx_data), .rx_data(rx_data), .transaction_done(transaction_done),
    .sclk(sclk), .mosi(mosi), .miso(miso), .ss_n(ss_n)
  );

  // Clock generation
  always #5 clk = ~clk;

  // Scoreboard
  class Scoreboard;
    // Store expected values
    logic [7:0] expected_data;
    // Adding expected value to the scoreboard
    task add_expected_value(logic [7:0] data);
      expected_data = data;
    endtask

    // Comparing actual value with expected value
    task compare(logic [7:0] actual_data);
      if (actual_data !== expected_data) begin
        $display("Mismatch! Expected: %d, Actual: %d", expected_data, actual_data);
      end else begin
        $display("Match! Expected: %d, Actual: %d", expected_data, actual_data);
      end
    endtask
  endclass

  Scoreboard scoreboard = new();

  // Test procedure
  initial begin
    // Initializing signals
    clk = 1;
    rst_n = 0;
    start_transaction = 0;
    tx_data = 8'hA5; // Example data to transmit
    miso = 1'b0;

    // Applying reset
    #10 rst_n = 1;

    // Waiting for some time and start the transaction
    start_transaction = 1;
    miso = 1;

    // Adding expected value to the scoreboard
    scoreboard.add_expected_value(8'd255); // Expected data to be received

    // Finishing the transaction
    #170 start_transaction = 0;
    
    // Comparing actual received data with expected data
    #20 scoreboard.compare(rx_data);

    #20; $finish;
  end

  // VCD dump for waveform viewing
  initial begin
    $dumpfile("spi.vcd");
    $dumpvars(0, spi_master_tb);
  end

endmodule
