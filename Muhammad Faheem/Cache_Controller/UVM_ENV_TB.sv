  //--------------------------------------------------------
  //TB_TOP Module
  //--------------------------------------------------------


`timescale 1ns/1ns

import uvm_pkg::*;
`include "uvm_macros.svh"


//--------------------------------------------------------
//Include Files
//--------------------------------------------------------
`include "interface.sv"
`include "seq_item.sv"
`include "sequence.sv"
`include "sequencer.sv"
`include "driver.sv"
`include "monitor.sv"
`include "agent.sv"
`include "scoreboard.sv"
`include "env.sv"
`include "test.sv"


module top;
  
  //--------------------------------------------------------
  //Instantiation
  //--------------------------------------------------------

  logic clock;
  
  intrf vif(.clk(clock));
  
  
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

  
  
  //--------------------------------------------------------
  //Interface Setting
  //--------------------------------------------------------
  initial begin
    uvm_config_db #(virtual intrf)::set(null, "*", "vif", vif);
    //-- Refer: https://www.synopsys.com/content/dam/synopsys/services/whitepapers/hierarchical-testbench-configuration-using-uvm.pdf
  end
  
  
  
  //--------------------------------------------------------
  //Start The Test
  //--------------------------------------------------------
  initial begin
    run_test("test");
  end
  
  
  //--------------------------------------------------------
  //Clock Generation
  //--------------------------------------------------------
  initial begin
    clock = 0;
    #5;
    forever begin
      clock = ~clock;
      #2;
    end
  end
  
  
  //--------------------------------------------------------
  //Maximum Simulation Time
  //--------------------------------------------------------
  initial begin
    #5000;
    $display("Sorry! Ran out of clock cycles!");
    $finish();
  end
  
  
  //--------------------------------------------------------
  //Generate Waveforms
  //--------------------------------------------------------
  initial begin
    $dumpfile("d.vcd");
    $dumpvars();
  end
  
  
  
endmodule: top

  //--------------------------------------------------------
  //Test Class
  //--------------------------------------------------------
class test extends uvm_test;
  `uvm_component_utils(test)

  env ev;
  base_sequence reset_seq;
  test_sequence test_seq;

  
  //--------------------------------------------------------
  //Constructor
  //--------------------------------------------------------
  function new(string name = "test", uvm_component parent);
    super.new(name, parent);
    `uvm_info("TEST_CLASS", "Inside Constructor!", UVM_HIGH)
  endfunction: new

  
  //--------------------------------------------------------
  //Build Phase
  //--------------------------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("TEST_CLASS", "Build Phase!", UVM_HIGH)

    ev = env::type_id::create("ev", this);

  endfunction: build_phase

  
  //--------------------------------------------------------
  //Connect Phase
  //--------------------------------------------------------
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("TEST_CLASS", "Connect Phase!", UVM_HIGH)

  endfunction: connect_phase

  
  //--------------------------------------------------------
  //Run Phase
  //--------------------------------------------------------
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("TEST_CLASS", "Run Phase!", UVM_HIGH)

    phase.raise_objection(this);

    //reset_seq
    reset_seq = base_sequence::type_id::create("reset_seq");
    reset_seq.start(ev.agnt.seqr);
    #10;

    repeat(15) begin
      //test_seq
      test_seq = test_sequence::type_id::create("test_seq");
      test_seq.start(ev.agnt.seqr);
      #10;
    end
    
    phase.drop_objection(this);

  endtask: run_phase


endclass

  //--------------------------------------------------------
  //Interface
  //--------------------------------------------------------
interface intrf(input bit clk);
    // Controller inputs
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

  //--------------------------------------------------------
  //Environment Class
  //--------------------------------------------------------
class env extends uvm_env;
  `uvm_component_utils(env)
  
  agent agnt;
 // scoreboard scb;
  
  
  //--------------------------------------------------------
  //Constructor
  //--------------------------------------------------------
  function new(string name = "env", uvm_component parent);
    super.new(name, parent);
    `uvm_info("ENV_CLASS", "Inside Constructor!", UVM_HIGH)
  endfunction: new
  
  
  //--------------------------------------------------------
  //Build Phase
  //--------------------------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("ENV_CLASS", "Build Phase!", UVM_HIGH)
    
    agnt = agent::type_id::create("agnt", this);
  //  scb = scoreboard::type_id::create("scb", this);
    
  endfunction: build_phase
  
  
  //--------------------------------------------------------
  //Connect Phase
  //--------------------------------------------------------
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("ENV_CLASS", "Connect Phase!", UVM_HIGH)
    
   // agnt.mon.monitor_port.connect(scb.scoreboard_port);
    
  endfunction: connect_phase
  
  
  //--------------------------------------------------------
  //Run Phase
  //--------------------------------------------------------
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    
  endtask: run_phase
  
  
endclass: env

  //--------------------------------------------------------
  //Sequencer Class
  //--------------------------------------------------------

class sequencer extends uvm_sequencer#(sequence_item);
  `uvm_component_utils(sequencer)
  
  
  //--------------------------------------------------------
  //Constructor
  //--------------------------------------------------------
  function new(string name = "sequencer", uvm_component parent);
    super.new(name, parent);
    `uvm_info("SEQR_CLASS", "Inside Constructor!", UVM_HIGH)
  endfunction: new
  
  
  //--------------------------------------------------------
  //Build Phase
  //--------------------------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("SEQR_CLASS", "Build Phase!", UVM_HIGH)
    
  endfunction: build_phase
  
  
  //--------------------------------------------------------
  //Connect Phase
  //--------------------------------------------------------
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("SEQR_CLASS", "Connect Phase!", UVM_HIGH)
    
  endfunction: connect_phase
  
  
  
endclass

  //--------------------------------------------------------
  //Agent Class
  //--------------------------------------------------------
class agent extends uvm_agent;
  `uvm_component_utils(agent)
  
  driver drv;
  monitor mon;
  sequencer seqr;
  
    
  //--------------------------------------------------------
  //Constructor
  //--------------------------------------------------------
  function new(string name = "agent", uvm_component parent);
    super.new(name, parent);
    `uvm_info("AGENT_CLASS", "Inside Constructor!", UVM_HIGH)
  endfunction: new
  
  
  //--------------------------------------------------------
  //Build Phase
  //--------------------------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("AGENT_CLASS", "Build Phase!", UVM_HIGH)
    
    drv = driver::type_id::create("drv", this);
    mon = monitor::type_id::create("mon", this);
    seqr = sequencer::type_id::create("seqr", this);
    
  endfunction: build_phase
  
  
  //--------------------------------------------------------
  //Connect Phase
  //--------------------------------------------------------
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("AGENT_CLASS", "Connect Phase!", UVM_HIGH)
    
    drv.seq_item_port.connect(seqr.seq_item_export);
    
  endfunction: connect_phase
  
  
  //--------------------------------------------------------
  //Run Phase
  //--------------------------------------------------------
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    
  endtask: run_phase
  
  
endclass

// Object class


class base_sequence extends uvm_sequence;
  `uvm_object_utils(base_sequence)
  
  sequence_item reset_pkt;
  
  //--------------------------------------------------------
  //Constructor
  //--------------------------------------------------------
  function new(string name= "base_sequence");
    super.new(name);
    `uvm_info("BASE_SEQ", "Inside Constructor!", UVM_HIGH)
  endfunction
  
  
  //--------------------------------------------------------
  //Body Task
  //--------------------------------------------------------
  task body();
    `uvm_info("BASE_SEQ", "Inside body task!", UVM_HIGH)
    
    reset_pkt = sequence_item::type_id::create("reset_pkt");
    start_item(reset_pkt);
    reset_pkt.randomize() with {reset==1;};
    finish_item(reset_pkt);
        
  endtask: body
  
  
endclass



class test_sequence extends base_sequence;
  `uvm_object_utils(test_sequence)
  
  //--------------------------------------------------------
  //Sequence Class
  //--------------------------------------------------------
  sequence_item item;
  
  //--------------------------------------------------------
  //Constructor
  //--------------------------------------------------------
  function new(string name= "test_sequence");
    super.new(name);
    `uvm_info("TEST_SEQ", "Inside Constructor!", UVM_HIGH)
  endfunction
  
  
  //--------------------------------------------------------
  //Body Task
  //--------------------------------------------------------
  task body();
    `uvm_info("TEST_SEQ", "Inside body task!", UVM_HIGH)
    
    item = sequence_item::type_id::create("item");
    start_item(item);
    item.randomize() with {reset==0;};
    finish_item(item);
        
  endtask: body
  
  
endclass

  //--------------------------------------------------------
  //Sequence Item Class
  //--------------------------------------------------------


class sequence_item extends uvm_sequence_item;
  `uvm_object_utils(sequence_item)

  //--------------------------------------------------------
  //Instantiation
  //--------------------------------------------------------
    bit reset;
    bit cpu_request;
    randc bit [31:0] address;
    randc bit [31:0] write_data;
    rand bit read;
    rand bit write;
    bit cache_flush;
    // Controller outputs
    bit [7:0] read_data;
    bit cache_hit;
    bit [2:0] cnt;
    bit flush_done;

  //--------------------------------------------------------
  //Default Constraints
  //--------------------------------------------------------
     // Constraint to ensure read and write are mutually exclusive
    constraint read_write_exclusive {
      address inside {32'h0000_1104,32'h0000_2208,32'h0000_330c,32'h0000_440f};
      (read == 1) <-> (write == 0);
      (write == 1) <-> (read == 0);
    }
  
  
  //--------------------------------------------------------
  //Constructor
  //--------------------------------------------------------
  function new(string name = "alu_sequence_item");
    super.new(name);

  endfunction: new

endclass

  //--------------------------------------------------------
  //Driver Class
  //--------------------------------------------------------
class driver extends uvm_driver#(sequence_item);
  `uvm_component_utils(driver)
  
  virtual intrf vif;
  sequence_item item;
  
  
  //--------------------------------------------------------
  //Constructor
  //--------------------------------------------------------
  function new(string name = "driver", uvm_component parent);
    super.new(name, parent);
    `uvm_info("DRIVER_CLASS", "Inside Constructor!", UVM_HIGH)
  endfunction: new
  
  
  //--------------------------------------------------------
  //Build Phase
  //--------------------------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("DRIVER_CLASS", "Build Phase!", UVM_HIGH)
    
    if(!(uvm_config_db #(virtual intrf)::get(this, "*", "vif", vif))) begin
      `uvm_error("DRIVER_CLASS", "Failed to get VIF from config DB!")
    end
    
  endfunction: build_phase
  
  
  //--------------------------------------------------------
  //Connect Phase
  //--------------------------------------------------------
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("DRIVER_CLASS", "Connect Phase!", UVM_HIGH)
    
  endfunction: connect_phase
  
  
  //--------------------------------------------------------
  //Run Phase
  //--------------------------------------------------------
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("DRIVER_CLASS", "Inside Run Phase!", UVM_HIGH)
    
    forever begin
      item = sequence_item::type_id::create("item"); 
      seq_item_port.get_next_item(item);
      drive(item);
      seq_item_port.item_done();
    end
    
  endtask: run_phase
  
  
  //--------------------------------------------------------
  //[Method] Drive
  //--------------------------------------------------------
  task drive(sequence_item item);
     @(posedge vif.clk);
      vif.rst = item.reset;
      vif.cpu_req = 1;
      vif.addr = item.address;
      vif.wr_data = item.write_data;
      vif.rd = item.read;
      vif.wr = item.write;
      vif.flush = 0;
      repeat(3) @(posedge vif.clk);
      vif.cpu_req = 0;
      vif.flush = 0;
  endtask: drive
  
  
endclass

  //--------------------------------------------------------
  //Monitor Class
  //--------------------------------------------------------
class monitor extends uvm_monitor;
  `uvm_component_utils(monitor)
  
  virtual intrf vif;
  sequence_item item;
  
  uvm_analysis_port #(sequence_item) monitor_port;
  
  
  //--------------------------------------------------------
  //Constructor
  //--------------------------------------------------------
  function new(string name = "monitor", uvm_component parent);
    super.new(name, parent);
    `uvm_info("MONITOR_CLASS", "Inside Constructor!", UVM_HIGH)
  endfunction: new
  
  
  //--------------------------------------------------------
  //Build Phase
  //--------------------------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("MONITOR_CLASS", "Build Phase!", UVM_HIGH)
    
    monitor_port = new("monitor_port", this);
    
    if(!(uvm_config_db #(virtual intrf)::get(this, "*", "vif", vif))) begin
      `uvm_error("MONITOR_CLASS", "Failed to get VIF from config DB!")
    end
    
  endfunction: build_phase
  
  //--------------------------------------------------------
  //Connect Phase
  //--------------------------------------------------------
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("MONITOR_CLASS", "Connect Phase!", UVM_HIGH)
    
  endfunction: connect_phase
  
  
  //--------------------------------------------------------
  //Run Phase
  //--------------------------------------------------------
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("MONITOR_CLASS", "Inside Run Phase!", UVM_HIGH)
    
    forever begin
      item = sequence_item::type_id::create("item");
      
      wait(!vif.rst);
      
      @(posedge vif.clk);
      wait(vif.cpu_req == 1);
      @(posedge vif.clk);
      item.cpu_request = vif.cpu_req;
      item.address = vif.addr;
      item.write_data = vif.wr_data;
      item.read = vif.rd;
      item.write = vif.wr;
      item.cache_flush = vif.flush;
      wait(vif.cpu_req == 0);
      repeat(3) @(posedge vif.clk);
      item.read_data = vif.rd_data;
      item.cache_hit = vif.hit;
      item.flush_done = vif.done;
      
      // send item to scoreboard
      monitor_port.write(item);
    end
        
  endtask: run_phase
  
  
endclass: monitor


