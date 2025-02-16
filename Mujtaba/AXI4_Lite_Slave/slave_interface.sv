interface slave_interface;

parameter ADDR_WIDTH = 32;
parameter DATA_WIDTH = 32;


logic clk;
logic reset;

//Write Address Channel
logic [ADDR_WIDTH-1:0]awaddr_i;
logic awvalid_i;

//Write Data Channel
logic [DATA_WIDTH-1:0]wdata_i;
logic wvalid_i;


//Write response channel
logic bready_i;
                                    


//Read address channel
logic [ADDR_WIDTH-1:0]araddr_i;
logic arvalid_i;


//Read data channel
logic rready_i;



/** -------------OUTPUTS-------------------- **/

//Write Address Channel
logic awready_o;

//Write Data Channel
logic wready_o;


//Write response channel
logic [1:0]bresp_o;

logic bvalid_o;


//Read address channel
logic arready_o;


//Read data channel
logic [DATA_WIDTH-1:0]rdata_o;//read data
logic [1:0]rresp_o;

logic rvalid_o;






endinterface
