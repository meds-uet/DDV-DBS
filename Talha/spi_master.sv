module spi_master #(
    parameter DATA_WIDTH = 8
)(
    input wire clk,
    input wire reset,
    input wire [DATA_WIDTH-1:0] data_in,
    input wire start,
    output reg [DATA_WIDTH-1:0] data_out,
    output reg sclk,
    output reg mosi,
    input wire miso,
    output reg ss
);

    // Internal signals
    reg [DATA_WIDTH-1:0] shift_reg;
    reg [3:0] bit_count;
    reg [2:0] state;
    
    // State machine states
    localparam IDLE = 3'b000;
    localparam LOAD = 3'b001;
    localparam TRANSFER = 3'b010;
    localparam COMPLETE = 3'b011;

    // SPI clock generation
    reg sclk_reg;
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            sclk_reg <= 1'b0;
        end else begin
            sclk_reg <= ~sclk_reg;
        end
    end

    // Main state machine
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= IDLE;
            shift_reg <= 0;
            bit_count <= 0;
            data_out <= 0;
            ss <= 1;
            sclk <= 0;
            mosi <= 0;
        end else begin
            case (state)
                IDLE: begin
                    ss <= 1;
                    sclk <= 0;
                    if (start) begin
                        state <= LOAD;
                    end
                end
                LOAD: begin
                    ss <= 0;
                    shift_reg <= data_in;
                    bit_count <= DATA_WIDTH;
                    state <= TRANSFER;
                end
                TRANSFER: begin
                    sclk <= sclk_reg;
                    if (sclk_reg) begin
                        mosi <= shift_reg[DATA_WIDTH-1];
                        shift_reg <= {shift_reg[DATA_WIDTH-2:0], miso};
                        bit_count <= bit_count - 1;
                        if (bit_count == 1) begin
                            state <= COMPLETE;
                        end
                    end
                end
                COMPLETE: begin
                    ss <= 1;
                    sclk <= 0;
                    data_out <= shift_reg;
                    state <= IDLE;
                end
            endcase
        end
    end

endmodule
