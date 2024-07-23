module level_pulse(input  logic clk,
                   input  logic rst_n,
                   input  logic level_i,
                   output logic pulse_o
                   );
    //enumarting the states
    typedef enum logic [1:0] 
    {IDLE    = 2'b00, 
     DETECT  = 2'b01} state_t;
    
    state_t current_state,next_state;
    reg level_p;   //state register to store input of past/previous edge

    always_ff @(posedge clk or negedge rst_n) begin

        if(~rst_n)begin
            current_state <= IDLE;
            level_p       <= 1'b0;
        end
        
        else begin
            current_state <= next_state;
            level_p       <= level_i;
        end
        
    end

    always_comb begin
        //next_state = current_state;
        pulse_o       = 1'b0;  //in order ot get output only when it is required

        case(current_state)

        IDLE: begin
            if(level_i && ~level_p) //checking input at previous and current edge of clock in order to transit to next state
                next_state = DETECT;
        end

        DETECT: begin //if this state occurs output gets high and next state is IDLE again
            pulse_o    = 1'b1;
            next_state = IDLE;
        end

        default next_state = IDLE; //defaulting the next_state to IDLE

        endcase
    end

endmodule