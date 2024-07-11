module Testbench_Shift_Register;


//Signals
logic clk;
logic reset;

logic data_in;
logic data_out;


//Instantiation
Shift_Register shift_register(

.clk(clk),
.reset(reset),
.data_in(data_in),
.data_out(data_out)

);

initial begin
    clock_generator();
end


initial begin
    reset_stimulus();

end





initial begin

@(negedge clk);

@(posedge clk);data_in = 1'b1;
@(posedge clk);data_in = 1'b0;
@(posedge clk);data_in = 1'b1;
@(posedge clk);data_in = 1'b1;

end





task clock_generator();

clk = 0;
forever #30 clk = ~clk;

endtask



task reset_stimulus();

reset = 1'b1;
//#40
//reset = 1'b0;

endtask




endmodule

