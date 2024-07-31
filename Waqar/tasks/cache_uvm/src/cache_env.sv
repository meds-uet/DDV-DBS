
class cache_env extends uvm_env;
    `uvm_component_utils(cache_env)

    //instantiate class
    cache_agent agent;

    //constructor
    function new(string name = "cache_env", uvm_component parent = null);
     super.new(name, parent);
    endfunction

    //build_phase
    function void build_phase(uvm_phase phase);
     super.build_phase(phase);
     `uvm_info(get_type_name(),"Inside the build_phase",UVM_LOW)//get_type_name will automatically get class name instead of we harcode here
     agent = cache_agent::type_id::create("agent", this);
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
