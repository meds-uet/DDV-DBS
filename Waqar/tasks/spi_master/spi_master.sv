module spi_master#(parameter DATA_WIDTH = 8)
                  (input  logic       clk,               //system clock
                   input  logic       rst_n,             //active low reset
                   input  logic       start_transaction, //signal for starting spi transaction
                   input  logic [DATA_WIDTH-1:0] tx_data,           //data to transmit to spi-slave
                   output logic [DATA_WIDTH-1:0] rx_data,           //data recieved from spi-slave
                   output logic       transaction_done,  //when trasmission+reception is done
                   output logic       sclk,              //spi-master clock
                   output logic       mosi,              //serail out from spi-master and vice versa for spi-slave
                   input  logic       miso,              //serial in  to   spi-master and vice versa for spi-slave
                   output logic       ss_n               //active slave-selector
                  );

  typedef enum logic [1:0] {IDLE, TRANSMIT, FINISH} state_t;  //total number of states
  state_t current_state, next_state;                          //state transitions

  logic [DATA_WIDTH-1:0] tx_shift_reg, rx_shift_reg; //datapath registers for transmission and reception
  logic [2:0] bit_counter;                //it is used inside transmission state to dictate its start and end
  logic sclk_en; //when it is enable our spi will work on sclk

  always_ff @(posedge clk or negedge rst_n) begin
    if(~rst_n) begin
        current_state <= IDLE;
    end
    else begin
      current_state   <= next_state;
    end
  end
  
  //next_state logic
  always_comb begin
    next_state = current_state;
    ss_n       = 1;
    transaction_done = 0;
    sclk_en    = 0;

    case(current_state)
    IDLE: begin
      if(start_transaction)begin
        transaction_done = 0;
        next_state       = TRANSMIT;
        ss_n             = 0;
      end

      else begin
        next_state = IDLE;
        ss_n       = 1;
      end
    end

    TRANSMIT: begin
      ss_n = 0; // Keeping slave select active
      sclk_en = 1; // Enabling sclk
      if (bit_counter == 3'd7) begin
        next_state = FINISH;
      end
    end

    FINISH: begin
      transaction_done  = 1'b1;
      next_state = IDLE;
    end

  endcase
  end

 // sclk generation
  always_ff @(posedge clk or negedge rst_n) begin
    if (~rst_n)
      sclk <= 0;
    else if (sclk_en)
      sclk <= ~sclk;
    else
      sclk <= 0;
  end

  // Shift registers and bit counter
  always_ff @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      tx_shift_reg <= 8'b0;
      rx_shift_reg <= 8'b0;
      bit_counter  <= 3'd0;
    end 
    
    else if (current_state == IDLE && start_transaction) begin
      tx_shift_reg <= tx_data;
      bit_counter <= 3'd0;
    end
    else if (current_state == TRANSMIT && sclk_en) begin
      if (sclk) begin
        // posedge sclk: shifting out next bit
        tx_shift_reg <= {tx_shift_reg[6:0], 1'b0};
        bit_counter  <= bit_counter + 3'd1;
      end 
      else begin
        // negedge sclk: shifting in next bit
        rx_shift_reg <= {rx_shift_reg[6:0], miso};
      end
    end
  end

  assign mosi = tx_shift_reg[7];
  assign rx_data = rx_shift_reg;

endmodule