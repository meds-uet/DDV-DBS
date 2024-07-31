//timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/11/2024 02:41:54 PM
// Design Name: 
// Module Name: spi_master
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

module spi_master
#(parameter CLK_DIVIDER = 4,
  parameter CPOL        = 0,
  parameter CPHA        = 0)
(
  input  logic       clk,
  input  logic       rst_n,
  input  logic       start_transaction,
  input  logic [7:0] tx_data,
  output logic [7:0] rx_data,
  output logic       transaction_done,
  output logic       sclk,
  output logic       mosi,
  input  logic       miso,
  output logic       ss_n,
  output logic [2:0] bit_count_o,
  output logic [1:0] state_o,
  output logic [7:0] rx_shift_o
);

  typedef enum logic [1:0] {IDLE, TRANSMIT, FINISH} state_t;
  state_t current_state, next_state;

  logic [7:0] tx_shift_reg, rx_shift_reg;
  logic [2:0] bit_count;
  logic [$clog2(CLK_DIVIDER)-1:0] posedge_count;
  reg sclk_reg;

  assign bit_count_o = bit_count;
  assign state_o = current_state;
  assign rx_shift_o = rx_shift_reg;

//  always_ff @(posedge clk or negedge rst_n) begin
//    if (!rst_n) begin
//      current_state <= IDLE;
//      tx_shift_reg <= 8'b0;
//      rx_shift_reg <= 8'b0;
//      sclk_reg <= 1'b0;
//      posedge_count <= 0;
//      bit_count <= 0;
//      transaction_done <= 1'b0;
//      ss_n <= 1'b1;
//    end else begin
//      current_state <= next_state;
//      if (current_state == TRANSMIT) begin
//        sclk_reg <= 1'b1;
//        posedge_count <= posedge_count + 1;
//        if (posedge_count == CLK_DIVIDER/2-1) begin
//          sclk_reg <= ~sclk_reg;
//        end else if (posedge_count == CLK_DIVIDER-1) begin
//          sclk_reg <= ~sclk_reg;
//          posedge_count <= 0;
//        end
//      end
//    end
//  end

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= IDLE;
    end else begin
      current_state <= next_state;
    end
  end

  // CLK_DIVIDER >= 4 and even
  always_ff @(posedge clk or negedge rst_n) begin
    if (current_state == TRANSMIT) begin
      if (posedge_count == CLK_DIVIDER/2-1) begin
        sclk_reg <= ~sclk_reg;
      end else if (posedge_count == CLK_DIVIDER-1) begin
        sclk_reg <= ~sclk_reg;
        bit_count <= bit_count + 1;
      end
      posedge_count <= (posedge_count + 1) % CLK_DIVIDER;
    end else begin
      sclk_reg = CPOL;
      bit_count <= 0;
      posedge_count <= 0;
    end
  end

  always_ff @(posedge sclk_reg or negedge sclk_reg) begin
    if (((sclk_reg == ~CPOL) & CPHA) | ((sclk_reg == CPOL) & ~CPHA)) begin
      tx_shift_reg <= {tx_shift_reg[6:0], 1'b0};
    end
    else begin // if (((sclk_reg == ~CPOL) & ~CPHA) | ((sclk_reg == CPOL) & CPHA)) begin
      rx_shift_reg <= {miso, rx_shift_reg[7:1]};
    end
  end

  always_comb begin
    case (current_state)
      IDLE: begin
        tx_shift_reg = 8'b0;
        rx_shift_reg = 8'b0;
        transaction_done = 1'b0;
        ss_n = 1'b1;
        if (start_transaction) begin
          next_state = TRANSMIT;
          tx_shift_reg = tx_data;
          ss_n = 1'b0;
        end
      end
      TRANSMIT: begin
//        if (sclk_reg == 1'b1) begin
//          rx_shift_reg = {miso, rx_shift_reg[7:1]};
//          tx_shift_reg = {tx_shift_reg[6:0], 1'b0};
//          bit_count = bit_count + 1;
//        end
        if (bit_count == 7) begin 
          next_state = FINISH;
          transaction_done = 1;
        end
      end
      FINISH: begin
        next_state = IDLE;
        rx_data = rx_shift_reg;
      end
      default: begin
        next_state = IDLE;
      end
    endcase
  end

  assign mosi = tx_shift_reg[7];
  assign sclk = sclk_reg;
endmodule