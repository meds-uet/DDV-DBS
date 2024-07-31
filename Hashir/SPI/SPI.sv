module spi_master #(
  parameter DATA_WIDTH = 8,      
  parameter CLOCK_DIVIDER = 8    
)(
  input  logic       clk,        
  input  logic       rst_n,      
  input  logic       start_transaction, 
  input  logic [DATA_WIDTH-1:0] tx_data, 
  output logic [DATA_WIDTH-1:0] rx_data, 
  output logic       transaction_done,   
  output logic       sclk,        
  output logic       mosi,        
  input  logic       miso,        
  output logic       ss_n         
);
  typedef enum logic [1:0] {IDLE, TRANSMIT, FINISH} state_t;
  state_t current_state, next_state;

  
  logic [DATA_WIDTH-1:0] tx_shift_reg; 
  logic [DATA_WIDTH-1:0] rx_shift_reg; 
  logic [3:0] bit_counter; 
  logic clk_div; 
  logic [31:0] clk_counter; 
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      clk_counter <= 0;
      clk_div <= 0;
    end 
    
    else if (clk_counter == (CLOCK_DIVIDER / 2 - 1)) begin
      clk_counter <= 0;
      clk_div <= ~clk_div; 
    end
    
    else begin
      clk_counter <= clk_counter + 1; 
    end
  end

  assign sclk = clk_div; 

 
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= IDLE; 
      tx_shift_reg <= 0;    
      rx_shift_reg <= 0;     
      bit_counter <= 0;      
      transaction_done <= 0; 
      ss_n <= 1;             
    end 
    
    else begin
      current_state <= next_state; 
      case (current_state)
        IDLE: begin
          if (start_transaction) begin
            tx_shift_reg <= tx_data; 
            rx_shift_reg <= 0;      
            bit_counter <= DATA_WIDTH - 1; 
            ss_n <= 0;               
            transaction_done <= 0; 
          end
        end
        TRANSMIT: begin
          if (clk_div) begin
            
            tx_shift_reg <= {tx_shift_reg[DATA_WIDTH-2:0], miso}; 
           
            rx_shift_reg <= {rx_shift_reg[DATA_WIDTH-2:0], mosi};
            bit_counter <= bit_counter - 1; 
          end
        end
        FINISH: begin
          ss_n <= 1;             
          transaction_done <= 1; 
        end
      endcase
    end
  end

 // Controller
  always_comb begin
    case (current_state)
      IDLE: begin
        if (start_transaction)
          next_state = TRANSMIT; 
        else
          next_state = IDLE; 
      end
      TRANSMIT: begin
        if (bit_counter == 0)
          next_state = FINISH; 
        else
          next_state = TRANSMIT; 
      end
      FINISH: begin
        if (!start_transaction)
          next_state = IDLE; 
        else
          next_state = FINISH; 
      end
    endcase
  end


  assign mosi = tx_shift_reg[DATA_WIDTH-1];
  assign rx_data = rx_shift_reg; 

endmodule