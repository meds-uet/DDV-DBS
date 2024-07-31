interface cache_interface #(parameter DATA_WIDTH = 32,
                            parameter ADDRESS_WIDTH = 32);
                            (input logic clk_i);
    logic rst_i;
    logic [ADDRESS_WIDTH-1:0] processor_addr; 
    logic wr_request; 
    logic rd_request; 
    logic [DATA_WIDTH-1:0] wr_data; 
    logic [DATA_WIDTH-1:0] rd_data;

endinterface

