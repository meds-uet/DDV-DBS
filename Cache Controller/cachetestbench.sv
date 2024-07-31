// Transaction Class
class transaction;
    rand bit read;
    rand bit write;
    rand bit flush;
    rand logic [31:0] address;
    rand logic [31:0] write_data;
    logic [31:0] read_data;
    logic hit;
    logic miss;
    logic ready;
    logic mem_read;
    logic mem_write;
    logic [31:0] mem_address;
    logic [31:0] mem_write_data;
    logic [31:0] mem_read_data;
    
    constraint c { 
        read dist {1 :/ 33, 0 :/ 33};
        write dist {1 :/ 33, 0 :/ 33};
        flush dist {1 :/ 33, 0 :/ 33};
    }
endclass

// Generator Class
class generator;
    transaction tr;
    mailbox #(transaction) mbx;
    int count = 0;
    int i = 0;
    
    function new(mailbox #(transaction) mbx);
        this.mbx = mbx;
        tr = new();
    endfunction;
    
    task run(); 
        repeat (count) begin
            assert (tr.randomize) else $error("Randomization failed");
            i++;
            mbx.put(tr);
            $display("[GEN] : Iteration : %0d read : %0d, write : %0d, flush : %0d, address : %0d, write_data : %0d", 
                i, tr.read, tr.write, tr.flush, tr.address, tr.write_data);
            @(next);
        end -> done;
    endtask
endclass

// Driver Class
class driver;
    virtual cache_if c_if;
    mailbox #(transaction) mbx;
    transaction tr;
    
    function new(mailbox #(transaction) mbx);
        this.mbx = mbx;
    endfunction;
    
    task reset();
        c_if.reset <= 1'b1;
        @(posedge c_if.clk);
        c_if.reset <= 1'b0;
        $display("[DRV] : DUT Reset Done");
        $display("------------------------------------------");
    endtask
    
    task drive();
        @(posedge c_if.clk);
        c_if.read <= tr.read;
        c_if.write <= tr.write;
        c_if.flush <= tr.flush;
        c_if.address <= tr.address;
        c_if.write_data <= tr.write_data;
        @(posedge c_if.clk);
        c_if.read <= 0;
        c_if.write <= 0;
        c_if.flush <= 0;
    endtask
    
    task run();
        forever begin
            mbx.get(tr);
            drive();
        end
    endtask
endclass

// Monitor Class
class monitor;
    virtual cache_if c_if;
    mailbox #(transaction) mbx;
    transaction tr;
    
    function new(mailbox #(transaction) mbx);
        this.mbx = mbx;
    endfunction;
    
    task run();
        tr = new();
        forever begin
            @(posedge c_if.clk);
            tr.read_data = c_if.read_data;
            tr.hit = c_if.hit;
            tr.miss = c_if.miss;
            tr.ready = c_if.ready;
            tr.mem_read = c_if.mem_read;
            tr.mem_write = c_if.mem_write;
            tr.mem_address = c_if.mem_address;
            tr.mem_write_data = c_if.mem_write_data;
            tr.mem_read_data = c_if.mem_read_data;
            mbx.put(tr);
            $display("[MON] : Read Data : %0d, Hit : %0d, Miss : %0d, Ready : %0d", 
                tr.read_data, tr.hit, tr.miss, tr.ready);
        end
    endtask
endclass

// Scoreboard Class
class scoreboard;
    mailbox #(transaction) mbx;
    transaction tr;
    event next;
    int err = 0;
    
    function new(mailbox #(transaction) mbx);
        this.mbx = mbx;
    endfunction;
    
    task run();
        forever begin
            mbx.get(tr);
            $display("[SCO] : Read Data : %0d, Hit : %0d, Miss : %0d, Ready : %0d", 
                tr.read_data, tr.hit, tr.miss, tr.ready);
            -> next;
        end
    endtask
endclass

// Environment Class
class environment;
    generator gen;
    driver drv;
    monitor mon;
    scoreboard sco;
    mailbox #(transaction) gdmbx;
    mailbox #(transaction) msmbx;
    event nextgs;
    virtual cache_if c_if;
    
    function new(virtual cache_if c_if);
        gdmbx = new();
        gen = new(gdmbx);
        drv = new(gdmbx);
        msmbx = new();
        mon = new(msmbx);
        sco = new(msmbx);
        this.c_if = c_if;
        drv.c_if = this.c_if;
        mon.c_if = this.c_if;
        gen.next = nextgs;
        sco.next = nextgs;
    endfunction
    
    task pre_test();
        drv.reset();
    endtask
    
    task test();
        fork
            gen.run();
            drv.run();
            mon.run();
            sco.run();
        join_any
    endtask
    
    task post_test();
        wait(gen.done.triggered);
        $display("---------------------------------------------");
        $display("Error Count :%0d", sco.err);
        $display("---------------------------------------------");
        $finish();
    endtask
    
    task run();
        pre_test();
        test();
        post_test();
    endtask
endclass

// Testbench Module
module tb;
    cache_if c_if();
    cache_controller dut (
        .clk(c_if.clk),
        .reset(c_if.reset),
        .read(c_if.read),
        .write(c_if.write),
        .flush(c_if.flush),
        .address(c_if.address),
        .write_data(c_if.write_data),
        .read_data(c_if.read_data),
        .hit(c_if.hit),
        .miss(c_if.miss),
        .ready(c_if.ready),
        .mem_read(c_if.mem_read),
        .mem_write(c_if.mem_write),
        .mem_address(c_if.mem_address),
        .mem_write_data(c_if.mem_write_data),
        .mem_read_data(c_if.mem_read_data)
    );
    
    initial begin
        c_if.clk <= 0;
    end
    
    always #10 c_if.clk <= ~c_if.clk;
    
    environment env;
    
    initial begin
        env = new(c_if);
        env.gen.count = 10;
        env.run();
    end
    
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
    end
endmodule
