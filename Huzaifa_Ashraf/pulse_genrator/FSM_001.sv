module FSM_001(
  input clk,
  input rst,
  input in,
  output reg detected
);

  // State definitions
  parameter S0 = 2'b00, S1 = 2'b01, S2 = 2'b10;

  reg [1:0] state, next_state;

  always @(posedge clk) begin    // Sequential part of design
    if (rst) begin
      state <= S0;
    end else begin
      state <= next_state;
    end
  end

  always @(*) begin
    case (state)
      S0:
        if (!in) begin
          next_state = S1;
        end else begin
          next_state = S0;
        end
      S1:
        if (in) begin
          next_state = S2;
        end else begin
          next_state = S1;
        end
      S2:
        if (in) begin
          next_state = S0;
        end else begin
          next_state = S1;
        end
      default:  // Default transition for unexpected cases
        next_state = S0;
    endcase
  end

  always @(state) begin  // Combinational logic for detected output
    case (state)
      S0: detected = 0;
      S1: detected = 0;
      S2: detected = 1;
    endcase
  end

endmodule
