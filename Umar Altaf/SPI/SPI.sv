`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/12/2024 12:31:13 PM
// Design Name: 
// Module Name: SPI
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


module SPI
#(parameter width=8)(
  input  logic       clk,
  input  logic       rst_n,
  input  logic       start_transaction,
  input  logic [width-1:0] tx_data,
  output logic [width-1:0] rx_data,
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

  always_ff @(posedge clk or negedge rst_n) begin
  if(rst_n)
  begin
  rx_data<=0;//mosi
  transaction_done<=0;
  ss_n<=1;
  bit_counter<=1;
  current_state<=IDLE;
  end  
 else if(sclk)
 begin  
 current_state<=next_state;
 end
 end

// begin
// if  (start_transaction)
//  begin
//  for(bit_counter=0;bit_counter<=7;bit_counter++)
//  begin
//  sclk<=1;
//  #5
//  sclk<=0;
//  end
//  end
//// TODO: Enter your code here
//  end
//end



//always_ff@(negedge sclk)
//begin
//rx_shift_reg<=rx_data<<1;
//tx_shift_reg<=tx_data<<1;
//end
  always_comb begin
// TODO: Control the state machine here
case(current_state)
IDLE:if(start_transaction)
begin
//  for(bit_counter=0;bit_counter<=7;bit_counter++)
//  begin
//  sclk=1;
//  #5
//  sclk=0;
//  end
tx_shift_reg=tx_data;// mosi 
  next_state=TRANSMIT;
  end
TRANSMIT:
begin
if((bit_counter!=0)&&sclk)
begin
repeat(8)

begin
ss_n=0;
tx_shift_reg=tx_shift_reg<<1;//mosi
rx_shift_reg={rx_shift_reg<<1,miso};//miso
bit_counter=bit_counter+1;
end
end
next_state=FINISH;
end
FINISH:
begin
rx_data=rx_shift_reg;//miso
transaction_done=1;
ss_n=1; 
next_state=IDLE;
end
endcase


  end

  assign mosi = tx_shift_reg[width-1];
  assign sclk = ( bit_counter !== 0 ) ? clk : 1'b0;

endmodule

