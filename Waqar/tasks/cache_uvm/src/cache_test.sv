
class cache_test extends uvm_test;
   //registering cache_test class with uvm_factory
   `uvm_component_utils(cache_test)

   //instantiate classes
   cache_env env;

   //constructor
   function new(string name = "cache_test", uvm_component parent = null);
    super.new(name, parent);
    `uvm_info(get_type_name(),"Inside the constructor",UVM_HIGH)
   endfunction

   //build_phase
   function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info(get_type_name(),"Inside the build_phase",UVM_HIGH)
    env = cache_env::type_id::create("env", this);
   endfunction

   //connect_phase
   function void connect_phase(uvm_phase phase)
    super.connect_phase(phase);
    `uvm_info(get_type_name(),"Inside the connect_phase",UVM_HIGH)
   endfunction

   //run_phase
   task run_phase(uvm_phase phase)
    super.run_phase(phase);
   endtask

endclass