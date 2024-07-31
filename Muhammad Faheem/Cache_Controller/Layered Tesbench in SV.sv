`include "interface.sv"
`include "env.sv"
module tb;
 
  intf vif();

  
    // Instantiate the cache controller
    cache_ctrl uut (
      .clk(vif.clk),
      .rst(vif.rst),
      .cpu_request(vif.cpu_req),
      .address(vif.addr),
      .write_data(vif.wr_data),
      .read(vif.rd),
      .write(vif.wr),
      .cache_flush(vif.flush),
      .read_data(vif.rd_data),
      .cache_hit(vif.hit),
      .cnt(vif.st_no),
      .flush_done(vif.done)
    );

 
  initial begin
    vif.clk <= 0;
  end
 
  always #10 vif.clk <= ~vif.clk;
 
  environment env;
 
  initial begin
    env = new(vif);
    env.gen.count = 10;
    env.run();
  end
 
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
endmodule



class transaction;
    bit cpu_request;
    rand bit [31:0] address;
    rand bit [31:0] write_data;
    rand bit read;
    rand bit write;
    bit cache_flush;
    // Controller outputs
    bit [7:0] read_data;
    bit cache_hit;
    bit [2:0] cnt;
    bit flush_done;
  
     // Constraint to ensure read and write are mutually exclusive
    constraint read_write_exclusive {
      address inside {32'h0000_1104,32'h0000_2208,32'h0000_330c,32'h0000_440f};
        (read == 1) -> (write == 0);
        (write == 1) -> (read == 0);
    }
  
   // Display function for input debugging
  function void display1(input string label);
    $display("[%s]: cpu_req: %b, cpu_addr: %h, wr_data: %h, read: %b, write: %b, flush_req: %b",label,cpu_request,address,write_data,read,write,cache_flush);    
  endfunction
  
     // Display function for ouput debugging
  function void display2(input string label);
    $display("[%s]: rd_data: %h, Hit: %b, State_no: %d, flush_done: %b",label,read_data,cache_hit,cnt,flush_done);    
  endfunction
  
endclass

interface intf;
    // Controller inputs
    logic clk;
    logic rst;
    logic cpu_req;
    logic [31:0] addr;
    logic [31:0] wr_data;
    logic rd;
    logic wr;
    logic flush;
    // Controller outputs
    logic [7:0] rd_data;
    logic hit;
    logic [2:0] st_no;
    logic done;

endinterface
  

`include "transaction.sv"
class generator;
  
  transaction tr;
  mailbox #(transaction) mbx;
  event done;
  int count = 0;
  event drvnext;
  
  // Constructor
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
    tr = new();
  endfunction
  
  // Task to generate transactions
  task run();
    repeat(count) begin
      assert(tr.randomize()) else $error("[GEN] :Randomization Failed");
      mbx.put(tr);
      tr.display1("GEN");
      tr.display2("GEN");
      @(drvnext);
    end
    -> done;
  endtask
  
endclass
 

class driver;
  
  virtual intf vif;
  transaction tr;
  mailbox #(transaction) mbx;
  event drvnext;
 
 
  // Constructor
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
  endfunction
  
  // Task to reset the driver
  task reset();
     vif.rst <= 1'b1;
     vif.cpu_req <= 1'b0;
     vif.rd<= 1'b0;
     vif.wr<= 1'b0;
     vif.flush<= 1'b0;
     repeat(3) @(posedge vif.clk);
     vif.rst <= 1'b0;
     repeat(2) @(posedge vif.clk);
 
    $display("[DRV] : RESET DONE");
    $display("-----------------------------------------");
  endtask
  
  // Task to drive transactions
  task run();
    forever begin
      mbx.get(tr);
      vif.cpu_req = 1;
      vif.addr = tr.address;
      vif.wr_data = tr.write_data;
      vif.rd = tr.read;
      vif.wr = tr.write;
      vif.flush = 0;
      repeat(3) @(posedge vif.clk);
      vif.cpu_req = 0;
      vif.flush = 0;
      repeat(3) @(posedge vif.clk);
      $display("[DRV]: Interface Triggered");
       repeat(3) @(posedge vif.clk);
      ->drvnext;
    end
  endtask
endclass
  
  
`include "generator.sv"
`include "driver.sv"
`include "monitor.sv"
class environment;

    generator gen;
    driver drv;
    monitor mon;
    //scoreboard sco;
 
    event nextgd; // gen -> drv
 
    mailbox #(transaction) mbxgd; // gen - drv

    virtual intf vif;
 
  // Constructor
  function new(virtual intf vif);
    mbxgd = new();
    gen = new(mbxgd);
    drv = new(mbxgd);
 
    mon = new();
  
 
    this.vif = vif;
    drv.vif = this.vif;
    mon.vif = this.vif;
 
    gen.drvnext = nextgd;
    drv.drvnext = nextgd;
  endfunction
 
  // Task to perform pre-test actions
  task pre_test();
    drv.reset();
  endtask
 
  // Task to run the test
  task test();
  fork
    gen.run();
    drv.run();
    mon.run();
  join_any
  endtask
 
  // Task to perform post-test actions
  task post_test();
    wait(gen.done.triggered);
    $finish();
  endtask
 
  // Task to start the test environment
  task run();
    pre_test();
    test();
    post_test();
  endtask
endclass


class monitor;
  transaction tr;
  //mailbox #(transaction) mbx;

 
  virtual intf vif;
 
  // Constructor
 // function new(mailbox #(transaction) mbx);
    //this.mbx = mbx;
 // endfunction
 
  // Task to monitor the bus
  task run();
    tr = new();
    forever begin
      @(posedge vif.clk);
      wait(vif.cpu_req == 1);
      @(posedge vif.clk);
      tr.cpu_request = vif.cpu_req;
      tr.address = vif.addr;
      tr.write_data = vif.wr_data;
      tr.read = vif.rd;
      tr.write = vif.wr;
      tr.cache_flush = vif.flush;
      wait(vif.cpu_req == 0);
      repeat(3) @(posedge vif.clk);
      tr.read_data = vif.rd_data;
      tr.cache_hit = vif.hit;
      tr.flush_done = vif.done;
      tr.display1("Mon");
      tr.display2("Mon");
      $display("-----------------------------------------");
      //$display("[MON] : DATA SENT : %0d", srx);
     // mbx.put(srx);
    end
  endtask
 
endclass
 
 