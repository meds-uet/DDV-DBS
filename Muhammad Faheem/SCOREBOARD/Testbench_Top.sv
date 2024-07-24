`include "generator.sv"
`include "interface.sv"
`include "driver.sv"
`include "monitor.sv"
`include "scoreboard.sv"
//`include "transaction.sv"

module testbench;

    add_if aif();
    driver drv;
    generator gen;
    monitor mon;
    scoreboard sb;
    event done;
    event trig;

    mailbox #(transaction) drv_mbx;
    mailbox #(transaction) mon_mbx;

    Add4 uut (
        .a(aif.a), 
        .b(aif.b), 
        .cin(aif.cin), 
        .s(aif.s), 
        .cout(aif.cout)
    );

    initial begin
        drv_mbx = new();
        mon_mbx = new();
        drv = new(drv_mbx);
        gen = new(drv_mbx);
        mon = new(mon_mbx);
        sb = new(mon_mbx);
        drv.aif = aif;
        mon.aif = aif;
        gen.next = trig;
        sb.next = trig;
        done = gen.done;
    end

    initial begin
        fork
            gen.run();
            drv.run();
            mon.run();
            sb.run();
        join_none
        wait(done.triggered);
        $finish();
    end

    initial begin
        $dumpfile("dump.vcd"); 
        $dumpvars;
    end

endmodule
