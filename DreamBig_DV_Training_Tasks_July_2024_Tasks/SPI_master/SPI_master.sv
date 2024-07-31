`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/19/2024 02:33:55 PM
// Design Name: 
// Module Name: SPI_master
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module spi_master #(width = 8)(
  input  logic       clk,
  input  logic       rst_n,
  input  logic       start_transaction,
  input  logic [width - 1:0] tx_data,
  output logic [width - 1:0] rx_data,
  output logic       transaction_done,
  output logic       sclk,
  output logic       mosi,
  input  logic       miso,
  output logic       ss_n
);

  typedef enum logic [1:0] {IDLE, TRANSMIT, FINISH} state_t;
  state_t current_state, next_state;

  logic [width - 1:0] tx_shift_reg, rx_shift_reg;
  logic [$clog2(width)-1:0] bit_counter;
  logic sclk_reg;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= IDLE;
      tx_shift_reg <= 8'b0;
      rx_shift_reg <= 8'b0;
      bit_counter <= 3'b0;
      sclk_reg <= 1'b0;
      transaction_done <= 1'b0;
      ss_n <= 1'b1;
    end else begin
      current_state <= next_state;
      if (current_state == TRANSMIT) begin
        sclk_reg <= ~sclk_reg;
        if (sclk_reg == 1'b1) begin                     // @ (posedge clk)
          tx_shift_reg <= {tx_shift_reg[width - 2:0], 1'b0};
          rx_shift_reg <= {rx_shift_reg[width - 2:0], miso};
          bit_counter <= bit_counter + 1;
        end
      end
    end
  end

  always_comb begin
    next_state = current_state;
    case (current_state)
      IDLE: begin
        if (start_transaction) begin
          next_state = TRANSMIT;
          tx_shift_reg = tx_data;
          ss_n = 1'b0;
        end
      end
      TRANSMIT: begin
        if (bit_counter == (width - 1)) begin
          next_state = FINISH;
        end
      end
      FINISH: begin
        transaction_done = 1'b1;
        ss_n = 1'b1;
        next_state = IDLE;
      end
    endcase
  end

  assign mosi = tx_shift_reg[width - 1];
  assign rx_data = rx_shift_reg;
  assign sclk = sclk_reg;

endmodule

