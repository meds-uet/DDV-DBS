class cache_sequence_item extends uvm_sequence_item;
    `uvm_object_utils(cache_sequence_item)

    //request--> inputs
    rand bit [31:0] processor_addr;
    rand bit [31:0] wr_data;
    rand bit wr_request;
    rand bit rd_request;

    //response--> outputs
    bit [31:0] rd_data;

    //constructor
    function new(string name = "cache_sequence_item");
     super.new(name);
    endfunction

endclass
