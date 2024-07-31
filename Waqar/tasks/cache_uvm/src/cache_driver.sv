
class cache_driver extends uvm_driver#(cache_sequence_item);
    `uvm_component_utils(cache_driver)
    
    //instantiate the interface
    cache_interface intf;

    //
    cache_sequence_item pkt;

    //constructor
    function new(string name = "cache_driver", uvm_component parent = null);
     super.new(name, parent);
    endfunction

    //build_phase
    function void build_phase(uvm_phase phase);
     super.build_phase(phase);
     `uvm_info(get_type_name(),"Inside the build_phase",UVM_LOW)//get_type_name will automatically get class name instead of we harcode here
     uvm_config_db #(virtual cache_interface)::get(null,"*","intf",intf);
     pkt = cache_sequence_item::type_id::create("pkt");
    endfunction

   //connect_phase
   function void connect_phase(uvm_phase phase)
    super.connect_phase(phase);
    `uvm_info(get_type_name(),"Inside the connect_phase",UVM_HIGH)
   endfunction

    //run_phase
    task run_phase(uvm_phase phase);
     
     forever begin
        @(posedge intf.clk_i)
          seq_item_port.get_next_item(pkt);
          intf.processor_addr <= pkt.processor_addr;
          intf.wr_data <= pkt.wr_data;
          intf.wr_request <= pkt.wr_request;
          intf.rd_request <= pkt.rd_request;
          seq_item_port.item_done();
     end

    endtask

endclass
