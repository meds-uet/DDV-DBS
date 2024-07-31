module tb_shift_reg;
    logic clk;
    logic rst;
    logic s_in;


    logic [3:0] q_out;

    shift_reg uut (
        .clk(clk),
        .rst(rst),
        .s_in(s_in),
        .q_out(q_out)
    );


    always begin 
        clk = 0;
        forever #10 clk = ~clk;
    end

    initial begin
        clk = 0;
        s_in = 0;
        rst = 1;
        #20 rst = 0;
        #20 s_in = 1;
        #20 s_in = 1;
        #20 s_in = 0;
        #20 s_in = 0;
   
        $finish;
    end



endmodule
