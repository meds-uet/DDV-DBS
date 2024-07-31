class cache_sequence extends uvm_sequence;
    `uvm_object_utils(cache_sequence)

    //instantiate cache_sequence_item class
    cache_sequence_item pkt;
    
    //constructor
    function new(string name = "cache_sequence");
     super.new(name);
    endfunction

    //body_task
    task body();
     // Sequence logic to generate transactions
        for (int i = 0; i < 32; i++) begin
            pkt = cache_sequence_item::type_id::create("pkt");
            pkt.processor_addr = i * 16;
            pkt.wr_data = $random;
            pkt.wr_request = 1;
            pkt.rd_request = 0;
            start_item(pkt);
            finish_item(pkt);
            #50;
            
            pkt.wr_request = 0;
            pkt.rd_request = 1;
            start_item(pkt);
            finish_item(pkt);
            #40;
        end
    endtask

endclass
