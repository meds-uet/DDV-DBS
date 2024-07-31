
class cache_agent extends uvm_agent;
    `uvm_component_utils(cache_agent)

    //instantiate classes
    cache_sequencer sequencer;
    cache_driver driver;
    cache_monitor monitor;

    //constructor
    function new(string name = "cache_agent", uvm_component parent = null);
     super.new(name, parent);
    endfunction

    //build_phase
    function void build_phase(uvm_phase phase);
    super.build_phase(phase);
     `uvm_info(get_type_name(),"Inside the build_phase",UVM_LOW)//get_type_name will automatically get class name instead of we harcode here
     sequencer = cache_sequencer::type_id::create("sequencer",this);
     driver    = driver::type_id::create("driver",this);
     monitor   = monitor::type_id::create("monitor",this);
    endfunction

    //connect_phase
    function void connect_phase(uvm_phase phase);
     super.connect_phase(phase);
     `uvm_info(get_type_name(),"Inside the connect_phase",UVM_HIGH)
     driver.seq_item_port.connect(sequencer.seq_item_export);
    endfunction

   //run_phase
   task run_phase(uvm_phase phase)
    super.run_phase(phase);
   endtask

endclass
