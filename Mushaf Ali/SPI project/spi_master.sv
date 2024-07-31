`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/15/2024 12:53:51 AM
// Design Name: 
// Module Name: spi
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
/*
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
//name assignment
typedef enum logic [1:0] {
IDLE=2'b00,
TRANSMIT=2'b01,
FINISH=2'b10} state_t;
state_t current_state, next_state;



//internal signals
logic [7:0] tx_shift_reg, rx_shift_reg;
logic [2:0] tx_count,rx_count;
logic [3:0] clk_div_count;
logic internal_clk_div;




//sclk generation

always_ff@(posedge clk)begin
if(rst_n)begin
clk_div_count<=0;
internal_clk_div<=0;
end else begin
clk_div_count<=clk_div_count+1;
if(clk_div_count==4'd8)begin
clk_div_count<=0;
internal_clk_div <= ~internal_clk_div;
end
end
end

assign sclk = internal_clk_div;


//state  operation in diffrent states
always_ff @(posedge clk or negedge rst_n) begin
if(rst_n)begin
ss_n<=1;
mosi<=0;
//sclk<=0;
current_state<=IDLE;
transaction_done<=0;
tx_count<=0;
rx_count<=0;
end
else begin
current_state<=next_state;

case(current_state)
IDLE : begin
if(start_transaction)begin
ss_n<=0;
mosi <= tx_shift_reg[7];
transaction_done<=0;
tx_count<=0;
rx_count<=0;
end
end

TRANSMIT : begin
if(sclk)begin
ss_n<=0;
transaction_done<=0;
tx_shift_reg <= {tx_shift_reg[6:0], 1'b0};
tx_count <= tx_count + 1;
end
else begin
ss_n<=0;
rx_shift_reg <= {rx_shift_reg[6:0], miso};
rx_count <= rx_count + 1;
end
end
FINISH : begin
if(tx_count==8 && rx_count==8)begin
ss_n<=1;
transaction_done<=1;
rx_data <= rx_shift_reg;
end
end
endcase
end

end
always_comb begin
case(current_state)
IDLE     :if(start_transaction) next_state=TRANSMIT ; else next_state=IDLE; 
TRANSMIT :if(tx_count==8 && rx_count==8) next_state=FINISH ; else next_state=TRANSMIT;
FINISH   :next_state=IDLE ;
default  :next_state=IDLE;
endcase
end
endmodule*/

//`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/15/2024 12:53:51 AM
// Design Name: 
// Module Name: spi_master
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: SPI Master Module
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////
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

  // State definitions
  typedef enum logic [1:0] {
    IDLE = 2'b00,
    TRANSMIT = 2'b01,
    FINISH = 2'b10
  } state_t;
  state_t current_state, next_state;

  // Internal signals
  logic [7:0] tx_shift_reg, rx_shift_reg;
  logic [2:0] tx_count, rx_count;
  logic [3:0] clk_div_count;
  logic internal_clk_div;

  // sclk generation
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      clk_div_count <= 0;
      internal_clk_div <= 0;
    end else begin
      clk_div_count <= clk_div_count + 1;
      if (clk_div_count == 4'd8) begin
        clk_div_count <= 0;
        internal_clk_div <= ~internal_clk_div;
      end
    end
  end

  assign sclk = internal_clk_div;

  // State operation in different states
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      ss_n <= 1;
      mosi <= 0;
      current_state <= IDLE;
      transaction_done <= 0;
      tx_count <= 0;
      rx_count <= 0;
      tx_shift_reg <= 0;
      rx_shift_reg <= 0;
    end else begin
      current_state <= next_state;

      case (current_state)
        IDLE: begin
          if (start_transaction) begin
            ss_n <= 0;
            tx_shift_reg <= tx_data;
            mosi <= tx_shift_reg[7];
            transaction_done <= 0;
            tx_count <= 0;
            rx_count <= 0;
          end
        end

        TRANSMIT: begin
          if (sclk) begin
            tx_shift_reg <= {tx_shift_reg[6:0], 1'b0};
            mosi <= tx_shift_reg[7];
            tx_count <= tx_count + 1;
          end else begin
            rx_shift_reg <= {rx_shift_reg[6:0], miso};
            rx_count <= rx_count + 1;
          end
        end

        FINISH: begin
          if (tx_count == 8 && rx_count == 8) begin
            ss_n <= 1;
            transaction_done <= 1;
            rx_data <= rx_shift_reg;
          end
        end
      endcase
    end
  end

  // State transition logic
  always_comb begin
    case (current_state)
      IDLE:     if (start_transaction) next_state = TRANSMIT; else next_state = IDLE;
      TRANSMIT: if (tx_count == 8 && rx_count == 8) next_state = FINISH; else next_state = TRANSMIT;
      FINISH:   next_state = IDLE;
      default:  next_state = IDLE;
    endcase
  end

endmodule
