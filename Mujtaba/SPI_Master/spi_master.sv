module spi_master#(parameter DATA_WIDTH = 8) (
  input  logic       clk,
  input  logic       reset,
  input  logic       start_transaction,
  input  logic [DATA_WIDTH-1:0] tx_data,
  output logic [DATA_WIDTH-1:0] rx_data,
  output logic       transaction_done,
  output logic       sclk,
  output logic       mosi,
  input  logic       miso,
  output logic       ss
);


  typedef enum logic [1:0] {IDLE, TRANSMIT, FINISH} state_t;
  state_t current_state, next_state;

  logic [DATA_WIDTH-1:0] tx_shift_reg, rx_shift_reg;
  logic [2:0] bit_counter;


  //Generating serial clock
  logic [3:0] CLK_DIV = 4'b0000;

  always @(posedge clk) begin
    if (CLK_DIV == 4'b0010) // Check if divider reaches 3 (binary: 0011)
        CLK_DIV <= 4'b0000; // Reset divider to 0
    else
        CLK_DIV <= CLK_DIV + 1; // Increment divider
   end

   assign sclk = (CLK_DIV == 4'b0010); // Output sclk when divider reaches 3



  // State machine logic
  always_ff @(posedge clk or negedge reset) begin
    if (reset) begin
      current_state <= IDLE;
    end else begin
      current_state <= next_state;
    end
  end

  always_comb begin
    next_state = current_state;
    case (current_state)
      IDLE: begin
        if (start_transaction) begin
          next_state = TRANSMIT;
        end
      end
      TRANSMIT: begin
        if (bit_counter == 3'd7 && sclk) begin
          next_state = FINISH;
        end
      end
      FINISH: begin
        next_state = IDLE;
      end
    endcase
  end

  // Shift register and bit counter logic
  always_ff @(posedge clk or negedge reset) begin
    if (reset) begin
      tx_shift_reg <= 8'b0;
      rx_shift_reg <= 8'b0;
      bit_counter <= 3'd0;
      transaction_done <= 0;
      ss <= 1;  // Deassert SS (active low)
    end else begin
      case (current_state)
        IDLE: begin
          ss <= 1;  // Deassert SS (active low)
          transaction_done <= 0;
          if (start_transaction) begin
            tx_shift_reg <= tx_data;
            bit_counter <= 3'd0;
            ss <= 0;  // Assert SS (active low)
          end
        end
        TRANSMIT: if (sclk) begin
          tx_shift_reg <= {tx_shift_reg[6:0], 1'b0};
          rx_shift_reg <= {rx_shift_reg[6:0], miso};
          bit_counter <= bit_counter + 1;
        end
        FINISH: begin
          ss <= 1;  // Deassert SS (active low)
          transaction_done <= 1;
          rx_data <= rx_shift_reg;
        end
      endcase
    end
  end

  assign mosi = tx_shift_reg[DATA_WIDTH-1];

endmodule

