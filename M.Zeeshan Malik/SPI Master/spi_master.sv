module spi_master (
  input  logic       clk,
  input  logic       rst_n,
  input  logic       start_transaction,
  input  logic [7:0] tx_data,
  output logic [7:0] rx_data,
  output logic       transaction_done,
  output logic       sclk,
  output logic       mosi,
  input  logic       miso,
  output logic       ss_n
);

  typedef enum logic [1:0] {IDLE, TRANSMIT, FINISH} state_t;
  state_t current_state, next_state;

  logic [7:0] tx_shift_reg, rx_shift_reg;
  logic [2:0] bit_counter;
  logic sclk_divider2;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      sclk_divider2 <= 1'b0;
      sclk <= 1'b0;
    end else begin
      sclk_divider2 <= ~sclk_divider2;
      sclk <= sclk_divider2;
    end
  end

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= IDLE;
    end else begin
      current_state <= next_state;
    end
  end
 
  always_comb begin
    next_state = current_state;
    ss_n = 1;
    transaction_done = 0;
    case (current_state)
      IDLE: begin
        if (start_transaction) begin
          next_state = TRANSMIT;
          ss_n = 0;
        end
      end
      TRANSMIT: begin
        if (bit_counter == 7 && sclk_divider2) begin
          next_state = FINISH;
        end
        ss_n = 0;
      end
      FINISH: begin
        next_state = IDLE;
        transaction_done = 1;
      end
    endcase
  end

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      tx_shift_reg <= 8'b0;
      rx_shift_reg <= 8'b0;
      bit_counter <= 3'b0;
    end else begin
      case (current_state)
        IDLE: begin
          tx_shift_reg <= tx_data;
          rx_shift_reg <= 8'b0;
          bit_counter <= 3'b0;
        end
        TRANSMIT: begin
          if (!sclk_divider2) begin
            tx_shift_reg <= tx_shift_reg << 1;
            mosi <= tx_shift_reg[7];
            bit_counter <= bit_counter + 1;
          end else if (sclk_divider2) begin
            rx_shift_reg <= {rx_shift_reg[6:0], miso};
          end
        end
        FINISH: begin
          // No specific actions required
        end
      endcase
    end
  end

  assign rx_data = rx_shift_reg;

endmodule
