module spi_master #(
  parameter DATA_WIDTH = 8,
  parameter CLOCK_DIVIDER = 4,
  parameter NUM_SLAVES = 4
)(
  input  logic                    clk,
  input  logic                    rst_n,
  input  logic                    start_transaction,
  input  logic [DATA_WIDTH-1:0]   tx_data,
  output logic [DATA_WIDTH-1:0]   rx_data,
  output logic                    transaction_done,
  output logic                    sclk,
  output logic                    mosi,
  input  logic                    miso,
  output logic [NUM_SLAVES-1:0]   ss_n,
  input  logic [$clog2(NUM_SLAVES)-1:0] slave_select
);

  typedef enum logic [1:0] {IDLE, TRANSMIT, FINISH} state_t;
  state_t current_state, next_state;

  logic [DATA_WIDTH-1:0] tx_shift_reg, rx_shift_reg;
  logic [$clog2(DATA_WIDTH)-1:0] bit_counter;
  logic [$clog2(CLOCK_DIVIDER)-1:0] clk_divider;
  logic sclk_internal, load_tx_data;

  // Clock generation for SPI
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      clk_divider <= '0;
      sclk_internal <= 1'b0;
    end else if (clk_divider == CLOCK_DIVIDER-1) begin
      clk_divider <= '0;
      sclk_internal <= ~sclk_internal;
    end else begin
      clk_divider <= clk_divider + 1'b1;
    end
  end

  assign sclk = (current_state == TRANSMIT) ? sclk_internal : 1'b0;

  // State machine
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      current_state <= IDLE;
    else
      current_state <= next_state;
  end

  always_comb begin
    next_state = current_state;
    transaction_done = 1'b0;
    ss_n = '1;
    case (current_state)
      IDLE: begin
        if (start_transaction) begin
          ss_n[slave_select] = 1'b0;
          next_state = TRANSMIT;
        end
      end
      TRANSMIT: begin
        ss_n[slave_select] = 1'b0;
        if (bit_counter == DATA_WIDTH - 1 && sclk_internal)
          next_state = FINISH;
      end
      FINISH: begin
        transaction_done = 1'b1;
        next_state = IDLE;
      end
    endcase
  end

  // Data loading and shift register logic
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      tx_shift_reg <= '0;
      rx_shift_reg <= '0;
      bit_counter <= '0;
      load_tx_data <= 1'b0;
    end else begin
      case (current_state)
        IDLE: begin
          load_tx_data <= 1'b1;
          bit_counter <= '0;
        end
        TRANSMIT: begin
          if (load_tx_data) begin
            tx_shift_reg <= tx_data;
            load_tx_data <= 1'b0;
          end else if (sclk_internal) begin
            tx_shift_reg <= {tx_shift_reg[DATA_WIDTH-2:0], 1'b0};
            rx_shift_reg <= {rx_shift_reg[DATA_WIDTH-2:0], miso};
            bit_counter <= bit_counter + 1'b1;
          end
        end
      endcase
    end
  end

  assign mosi = tx_shift_reg[DATA_WIDTH-1];
  assign rx_data = rx_shift_reg;

endmodule