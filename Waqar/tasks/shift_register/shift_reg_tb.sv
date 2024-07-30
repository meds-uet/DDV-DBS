module shift_reg_tb;

    reg clk_i;
    reg rst_i;
    reg d_i;
    wire q_o;

    initial begin
        clk_i = 1;
        forever #10 clk_i = ~clk_i;
    end

    shift_reg_4b dut (
        .clk_i(clk_i), 
        .rst_i(rst_i),
        .d_i(d_i),
        .q_o(q_o)
    );

    initial begin
        rst_i = 0;
        d_i = 0;
        #10;
        rst_i = 1;
        @(posedge clk_i)d_i = 1'b1;
        @(posedge clk_i)d_i = 1'b0;
        @(posedge clk_i)d_i = 1'b1;
        //#10;
        //d_i = 3'b111;
        
        #100;
        $finish;
    end

    initial begin
        $dumpfile("reg.vcd");
        $dumpvars(0, shift_reg_tb);
    end

endmodule
