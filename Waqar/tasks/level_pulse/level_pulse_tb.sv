//to be modified

module level_pulse_tb;

    reg clk;
    reg rst_n;
    reg level_i;
    wire pulse_o;

   
    level_pulse dut
(
    .clk(clk),
    .rst_n(rst_n),
    .level_i(level_i),
    .pulse_o(pulse_o)
);
    //clock generation
    always #10 clk = ~clk;
     
    initial begin
        clk   = 1'b0;
        rst_n = 1'b0;
        level_i = 1'b0;
        #10;
        rst_n = 1'b1;
        level_i = 1'b0;
        #10;
        level_i = 1'b1;
        #20;
        level_i = 1'b0;
        #20;
        level_i = 1'b1;
        #100;

        $finish;
    end
    
    //generating .vcd file and dumping the variables for gtkwave
    initial begin
        $dumpfile("level_pulse.vcd");
        $dumpvars(0,"level_pulse_tb");
    end
    
endmodule