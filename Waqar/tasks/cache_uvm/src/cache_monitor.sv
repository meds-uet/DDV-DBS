
class cache_monitor extends uvm_monitor;
    `uvm_component_utils(cache_monitor)
    
    //instantiate the interface
    cache_interface intf;
    cache_sequence_item pkt;

    //create a port
    uvm_analysis_port #(cache_sequence_item) monitor_port;

    //constructor
    function new(string name = "cache_monitor", uvm_component parent = null);
     super.new(name, parent);
    endfunction

    //build_phase
    function void build_phase(uvm_phase phase);
     super.build_phase(phase);
     `uvm_info(get_type_name(),"Inside the build_phase",UVM_HIGH)
     uvm_config_db #(virtual cache_interface)::get(null,"*","intf",intf);

     pkt = cache_sequence_item::type_id::create("pkt");

     monitor_port = new("Monitor_Port", this);
    endfunction

   //connect_phase
   function void connect_phase(uvm_phase phase)
    super.connect_phase(phase);
    `uvm_info(get_type_name(),"Inside the connect_phase",UVM_HIGH)
   endfunction

    //run_phase
    task run_phase(uvm_phase phase);
     forever begin
        @(posedge intf.clk_i);
          pkt.processor_addr <= intf.processor_addr;
          pkt.wr_data <= intf.wr_data;
          pkt.wr_request <= intf.wr_request;
          pkt.rd_request <= intf.rd_request;
     end
    endtask

endclass
