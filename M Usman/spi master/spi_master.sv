module spi_master #(
  parameter DATA_WIDTH = 8,      // Data width for SPI transactions
  parameter CLOCK_DIVIDER = 8    // Clock divider for SPI clock rate
)(
  input  logic       clk,        // System clock
  input  logic       rst_n,      // Active-low reset
  input  logic       start_transaction, // Start transaction signal
  input  logic [DATA_WIDTH-1:0] tx_data, // Data to transmit
  output logic [DATA_WIDTH-1:0] rx_data, // Received data
  output logic       transaction_done,   // Transaction completion flag
  output logic       sclk,        // SPI clock
  output logic       mosi,        // Master Out Slave In
  input  logic       miso,        // Master In Slave Out
  output logic       ss_n         // Slave Select (active low)
);

  // State enumeration for the SPI state machine
  typedef enum logic [1:0] {IDLE, TRANSMIT, FINISH} state_t;
  state_t current_state, next_state;

  // Shift registers for transmitting and receiving data
  logic [DATA_WIDTH-1:0] tx_shift_reg; // Shift register for transmit data
  logic [DATA_WIDTH-1:0] rx_shift_reg; // Shift register for received data
  logic [3:0] bit_counter; // Counter to track bits transmitted/received

  // Clock divider for generating SPI clock
  logic clk_div; // Divided clock signal for SPI
  logic [31:0] clk_counter; // Counter for clock division

  // Clock divider logic to generate SPI clock
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      clk_counter <= 0;
      clk_div <= 0;
    end else if (clk_counter == (CLOCK_DIVIDER / 2 - 1)) begin
      clk_counter <= 0;
      clk_div <= ~clk_div; // Toggle clock divider output
    end else begin
      clk_counter <= clk_counter + 1; // Increment counter
    end
  end

  assign sclk = clk_div; // Assign the SPI clock output

  // SPI state machine
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= IDLE; // Reset state
      tx_shift_reg <= 0;     // Clear transmit shift register
      rx_shift_reg <= 0;     // Clear receive shift register
      bit_counter <= 0;      // Reset bit counter
      transaction_done <= 0; // Clear transaction done flag
      ss_n <= 1;             // Deactivate slave select (high)
    end else begin
      current_state <= next_state; // Update current state
      case (current_state)
        IDLE: begin
          if (start_transaction) begin
            tx_shift_reg <= tx_data; // Load data to transmit
            rx_shift_reg <= 0;       // Clear receive shift register
            bit_counter <= DATA_WIDTH - 1; // Set bit counter to number of bits
            ss_n <= 0;               // Activate slave select (low)
            transaction_done <= 0;  // Clear transaction done flag
          end
        end
        TRANSMIT: begin
          if (clk_div) begin
            // Shift out data and capture MISO
            tx_shift_reg <= {tx_shift_reg[DATA_WIDTH-2:0], miso}; 
            // Shift in data from MOSI
            rx_shift_reg <= {rx_shift_reg[DATA_WIDTH-2:0], mosi};
            bit_counter <= bit_counter - 1; // Decrement bit counter
          end
        end
        FINISH: begin
          ss_n <= 1;              // Deactivate slave select (high)
          transaction_done <= 1; // Set transaction done flag
        end
      endcase
    end
  end

  // Next state logic for the SPI state machine
  always_comb begin
    case (current_state)
      IDLE: begin
        if (start_transaction)
          next_state = TRANSMIT; // Move to TRANSMIT state if transaction starts
        else
          next_state = IDLE; // Stay in IDLE state otherwise
      end
      TRANSMIT: begin
        if (bit_counter == 0)
          next_state = FINISH; // Move to FINISH state when all bits are transmitted
        else
          next_state = TRANSMIT; // Continue in TRANSMIT state otherwise
      end
      FINISH: begin
        if (!start_transaction)
          next_state = IDLE; // Move to IDLE state when transaction is done
        else
          next_state = FINISH; // Stay in FINISH state otherwise
      end
    endcase
  end

  // Assign output signals
  assign mosi = tx_shift_reg[DATA_WIDTH-1]; // Assign MOSI to the MSB of the shift register
  assign rx_data = rx_shift_reg; // Output the received data

endmodule
