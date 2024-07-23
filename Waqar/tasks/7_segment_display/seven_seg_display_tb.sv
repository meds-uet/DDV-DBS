module seven_seg_display_tb;

    reg [3:0] a_i;
    wire [6:0] seg_o;

    seven_seg_display dut   (.a_i(a_i),
                             .seg_o(seg_o));
    integer i;

    initial begin
        for(i=0; i<16; i++) begin
            a_i = i;
            #10;
            $display("Input value: %d, Segments: %b", a_i, seg_o);
        end
    end
        
    initial begin
        $dumpfile("seven_seg_display.vcd");
        $dumpvars(0,seven_seg_display_tb);
    end


endmodule
