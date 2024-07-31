`timescale 1ns / 1ps
module tb_seven_segment_decoder;

    logic [3:0] bin;
    logic [6:0] seg;

    seven_segment_decoder uut (
        .bin(bin),
        .seg(seg)
    );

    initial begin
        apply_inputs();
        $finish;
    end

    task apply_inputs();
        for (int i = 0; i < 16; i++) begin
            bin = i;
            #10;
        end
    endtask

    task monitor_outputs();
        $monitor("bin = %b, seg = %b", bin, seg);
    endtask

    initial begin
        monitor_outputs();
    end

endmodule

