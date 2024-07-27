module spi_master #(parameter DATA_WIDTH = 8) (
  input  logic             clk,
  input  logic             rst_n,
  input  logic             start_transaction,
  input  logic [DATA_WIDTH-1:0] tx_data,
  output logic [DATA_WIDTH-1:0] rx_data,
  output logic             transaction_done,
  output logic             sclk,
  output logic             mosi,
  input  logic             miso,
  output logic             ss_n
);

  typedef enum logic [1:0] {IDLE, TRANSMIT, FINISH} state_t;
  state_t current_state, next_state;

  logic [DATA_WIDTH-1:0] tx_shift_reg, rx_shift_reg;
  logic [clog2(DATA_WIDTH):0] bit_counter;
  logic sclk_enable;

  // State machine and shift registers
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= IDLE;
      tx_shift_reg <= 0;
      rx_shift_reg <= 0;
      bit_counter <= 0;
      transaction_done <= 0;
      sclk_enable <= 0;
      ss_n <= 1;
    end else begin
      current_state <= next_state;

      case (current_state)
        IDLE: begin
          transaction_done <= 0;
          if (start_transaction) begin
            tx_shift_reg <= tx_data;
            bit_counter <= 0;
            sclk_enable <= 1;
            ss_n <= 0;
          end
        end
        TRANSMIT: begin
          sclk_enable <= ~sclk_enable;
          if (sclk_enable) begin
            tx_shift_reg <= {tx_shift_reg[DATA_WIDTH-2:0], 1'b0};
            rx_shift_reg <= {rx_shift_reg[DATA_WIDTH-2:0], miso};
            bit_counter <= bit_counter + 1;
          end
        end
        FINISH: begin
          transaction_done <= 1;
          sclk_enable <= 0;
          ss_n <= 1;
        end
      endcase
    end
  end

  always_comb begin
    next_state = current_state;
    case (current_state)
      IDLE: if (start_transaction) next_state = TRANSMIT;
      TRANSMIT: if (bit_counter == DATA_WIDTH) next_state = FINISH;
      FINISH: if (!start_transaction) next_state = IDLE;
    endcase
  end

  assign mosi = tx_shift_reg[DATA_WIDTH-1];
  assign sclk = sclk_enable && (current_state == TRANSMIT);
  assign rx_data = rx_shift_reg;

endmodule
