module tb_parameterized_counter;
parameter WIDTH = 8;
logic up;
logic clk;
logic down;
logic reset;
logic [WIDTH-1 :0] Initialvalue;
logic [WIDTH-1: 0] count;
int i;

parameterized_counter #(
    .WIDTH(WIDTH)
    ) uut(
    .up(up),
    .cl(clk),
    .down(down),
    .reset(reset),
    .Initialvalue(Initiavalue),
    .count(count)
);

always #5 clk = ~clk;

initial begin
    clk = 0;
    reset = 0;
    up = 0;
    down = 0;
    for(i =0; i < 4; i = i +1) begin
    Initialvalue = i;
    reset = 1;
    
    #10
    reset = 0;
    up = 1;
    #10
    up = 0;
    down = 1;
    #10
    down = 0;
    up = 1;
    #10
    up = 1;
    down = 1;
    #10
    up = 0;
    down = 0;
    end
    $finish:
end

initial begin
    $monitor("Time = %0t , reset = %0t , initial value = %b, up = %b, down = %b, count = %h", $time, reset, Initialvalue, up, down, count);

end
endmodule 
