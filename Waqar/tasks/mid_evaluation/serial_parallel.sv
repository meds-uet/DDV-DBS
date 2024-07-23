module serial_to_parallel #(
    parameter WIDTH = 8
) (
    input  logic clk,
    input  logic rst_n, //active low reset
    input  logic serial_in, //serial input
    input  logic msb_first, 
    output logic [WIDTH-1:0] parallel_out, //parallel output
    output logic data_valid
);

    logic [WIDTH-1:0] shift_reg; //register to store input values before passing them to output
    logic [$clog2(WIDTH):0] bit_count; 

    always_ff @(posedge clk) begin
        if(~rst_n)begin
            shift_reg <= '0;
            bit_count <= 4'b0000;
            data_valid <= 1'b0;
        end

        else begin

            if(msb_first & bit_count != 4'b1000) begin //checks if msb_first = 1 to store data from msb side and if counter hasn't exceeded its limit
                data_valid <= 1'b1;
                shift_reg <= {serial_in, shift_reg[WIDTH-1:1]};
                bit_count <= bit_count +1;
            end

            else if(!msb_first & bit_count != 4'b1000) begin //checks if msb_first = 0 to store data from lsb side and if counter hasn't exceeded its limit
                data_valid <= 1'b1;
                shift_reg <= {shift_reg[WIDTH-2:0], serial_in};
                bit_count <= bit_count +1;
            end

            else begin
                data_valid <= 1'b0;
                bit_count <= 4'b0000;
            end

        end

    assign parallel_out = shift_reg; //assigning output 
        
    end
endmodule
