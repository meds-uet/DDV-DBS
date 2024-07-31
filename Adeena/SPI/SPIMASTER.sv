module spi_master #(
  parameter DATA_WIDTH = 8,
  parameter CLOCK_DIVIDER = 4, // SPI Clock rate control
  parameter NUM_SLAVES = 1
)(
  input  logic       clk,
  input  logic       rst_n,
  input  logic       start_transaction,
  input  logic [7:0] tx_data,
  output logic [7:0] rx_data,
  output logic       transaction_done,
  output logic       sclk,
  output logic       mosi,
  input  logic       miso,
  output logic [NUM_SLAVES-1:0] ss_n
);

  typedef enum logic [1:0] {IDLE, TRANSMIT, FINISH} state_t;
  state_t current_state, next_state;

  logic [7:0] tx_shift_reg, rx_shift_reg;
  logic [2:0] bit_counter;
  logic [CLOCK_DIVIDER-1:0] clk_divider;
  logic sclk_edge;
  logic load_tx_data;

  // Clock generation for SPI
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      clk_divider <= 0;
    else if (clk_divider == CLOCK_DIVIDER-1)
      clk_divider <= 0;
    else
      clk_divider <= clk_divider + 1;
  end

  // Generate SPI clock (sclk) with the desired frequency
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      sclk_edge <= 0;
    else if (clk_divider == (CLOCK_DIVIDER >> 1) - 1)
      sclk_edge <= ~sclk_edge;
  end

  assign sclk = sclk_edge;

  // State machine
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      current_state <= IDLE;
    else
      current_state <= next_state;
  end

  always_comb begin
    next_state = current_state;
    transaction_done = 1'b0; // Default value
    ss_n = {NUM_SLAVES{1'b1}}; // Default value
    case (current_state)
      IDLE: begin
        if (start_transaction) begin
          ss_n = {NUM_SLAVES{1'b0}};
          next_state = TRANSMIT;
        end
      end
      TRANSMIT: begin
        ss_n = {NUM_SLAVES{1'b0}};
        if (bit_counter == (DATA_WIDTH - 1))
          next_state = FINISH;
      end
      FINISH: begin
        transaction_done = 1'b1;
        next_state = IDLE;
      end
    endcase
  end

  // Data loading on state transition
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      tx_shift_reg <= 8'd0;
      bit_counter <= 3'd0;
      load_tx_data <= 1'b0;
    end
    else if (current_state == IDLE) begin
      load_tx_data <= 1'b1;
	  tx_shift_reg <= 0;
	  bit_counter <= 3'd0; 
	  rx_shift_reg <= 0;
    end
    else if (current_state == TRANSMIT) begin
     if (load_tx_data) begin
      tx_shift_reg <= tx_data; // Load tx_data into shift register
	  load_tx_data <= 0;
    end
  end
end

  // Shift register logic
  always_ff @(negedge sclk or negedge rst_n) begin
    if (!rst_n) begin
      tx_shift_reg <= 8'd0;
      bit_counter <= 3'd0;
    end
    else if (current_state == TRANSMIT) begin
      tx_shift_reg <= tx_shift_reg[DATA_WIDTH-1:0] << 1; // Shift out the MSB
      bit_counter <= bit_counter + 1;
    end
  end

  always_ff @(posedge sclk or negedge rst_n) begin
    if (!rst_n)
      rx_shift_reg <= 8'd0;
    else if (current_state == TRANSMIT)
      rx_shift_reg <= {rx_shift_reg[DATA_WIDTH-2:0], miso}; // Shift in data from MISO
  end

  assign mosi = tx_shift_reg[DATA_WIDTH-1]; // MSB of tx_shift_reg to MOSI
  assign rx_data = rx_shift_reg;

endmodule
