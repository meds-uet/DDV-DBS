module AXI4_LITE_SLAVE#(parameter ADDR_WIDTH = 32,
                          parameter DATA_WIDTH = 32)(


/** -------------INPUTS-------------------- **/

input clk,
input reset,

//Write Address Channel
input [ADDR_WIDTH-1:0]awaddr_i,//specififes address where write operation will occur
input awvalid_i,//master asserts it when it wants to initiate write operation

//Write Data Channel
input [DATA_WIDTH-1:0]wdata_i,//write datas
input wvalid_i,//The master asserts (wvalid = 1) when it wants to initiate the data transfer for the write operation


//Write response channel
input bready_i,//write response ready ,  Indicates whether the master is ready to accept the write response (bresp) from the slave
                    //The master asserts (bready = 1) when it is ready to receive and process the response from the slave                 


//Read address channel
input [ADDR_WIDTH-1:0]araddr_i,//read address
input arvalid_i,//Indicates that the read address (araddr) and associated control signals (arprot) are valid and should be processed by the slave.
                //The master asserts (arvalid = 1) when it wants to initiate a read operation.


//Read data channel
input rready_i,//Indicates whether the master is ready to accept the read data (rdata) and response status (rresp) from the slave
                    //The master asserts (rready = 1) when it is ready to receive and process the read data and response from the slave



/** -------------OUTPUTS-------------------- **/

//Write Address Channel
output logic awready_o,//slave asserts it when it is ready to accept a valid write address and begin write operation

//Write Data Channel
output logic wready_o,//Indicates whether the slave is ready to accept write data
                      //The slave asserts (wready = 1) when it is ready to accept valid write data and begin processing the data transfer


//Write response channel
output logic [1:0]bresp_o,//Typically includes responses like OKAY (successful write), EXOKAY (exclusive access okay), SLVERR (slave error), or DECERR (decode error)
                   //Usually a few bits wide, enough to encode possible response statuses

output logic bvalid_o,//write response valid , Indicates that the write response (bresp) from the slave is valid and should be read by the master
                    //The slave asserts (bvalid = 1) when it has a valid response status to report to the master


//Read address channel
output logic arready_o,//Indicates whether the slave is ready to accept a read address and associated control signals from the master
                       //The slave asserts (arready = 1) when it is ready to accept a valid read address and begin processing the read operation


//Read data channel
output logic [DATA_WIDTH-1:0]rdata_o,//read data
output logic [1:0]rresp_o,//Typically includes responses like OKAY (successful write), EXOKAY (exclusive access okay), SLVERR (slave error), or DECERR (decode error)
                   //Usually a few bits wide, enough to encode possible response statuses

output logic rvalid_o//Indicates that the read data (rdata) and associated response status (rresp) are valid and should be read by the master                 
                    //The slave asserts (rvalid = 1) when it has valid read data and response status to report to the master


);



//Internal memory mapped registers
logic [DATA_WIDTH-1:0]register[3:0];



//-------------------------------------------------------


//Write Operation
always_ff @(posedge clk or posedge reset) begin
    if(reset) begin
        register[0] <= 32'h0;
	register[1] <= 32'h0;
	register[2] <= 32'h0;
	register[3] <= 32'h0;

        awready_o <= 1'b0;
        wready_o <= 1'b0;
        bvalid_o <= 1'b0;
        bresp_o <= 2'b00; // (OKAY)
    end 

    else begin
        awready_o <= 1'b0;
        wready_o <= 1'b0;
        bvalid_o <= 1'b0;

        if(awvalid_i && wvalid_i) begin
            awready_o <= 1'b1;
            wready_o <= 1'b1;
            bvalid_o <= 1'b1;
            bresp_o <= 2'b00; // (OKAY)

            if (bready_i) begin
                //Check for valid address
                if (awaddr_i != 32'h00000000 && awaddr_i != 32'h00000004 && awaddr_i != 32'h00000008 && awaddr_i != 32'h0000000C || awvalid_i == 1'b0) begin
                    bresp_o <= 2'b10; // (SLVERR)
                end
                //Check for valid data
                else if (wdata_i > 32'hFFFFFFFF || wvalid_i == 1'b0) begin
                    bresp_o <= 2'b10; // (SLVERR)
                end
                //If both address and data are valid, perform the write
                else begin
                 

		    if (awaddr_i == 32'h00000000) 
                		register[0] <= wdata_i;     
            	    else if (awaddr_i == 32'h00000004) 
<<<<<<< HEAD
                		register[1] <= wdata_i;   
            	    else if (awaddr_i == 32'h00000008) 
                		register[2] <= wdata_i;   
                    else if (awaddr_i == 32'h0000000C) 
                		register[3] <= wdata_i;
=======
                		register[1] <= wdata_i;    
            	    else if (awaddr_i == 32'h00000008) 
                		register[2] <= wdata_i;   
                    else if (awaddr_i == 32'h0000000C) 
                		register[3] <= wdata_i;   
>>>>>>> 536614259bf5a5837f38d1dc9b9c62ef767aa5b5

                    bresp_o <= 2'b00; // (OKAY)
                end
            end
		
	    else begin
		bresp_o <= 2'b10;
	    end
        end

	//If both address and data are invalid 
        if (!awvalid_i || !wvalid_i) begin
            awready_o <= 1'b0;
            wready_o <= 1'b0;
            bvalid_o <= 1'b0;
            bresp_o <= 2'b10; // (SLVERR)
        end
    end
end

//-------------------------------------------------------



//Read Operation
always_comb begin

	if(reset) begin
		rdata_o = 32'h00000000;
		arready_o = 1'b0;
		rvalid_o = 1'b0;
		rresp_o = 2'b00;//(OKAY)
	end

	else begin

		if(arvalid_i) begin
            		arready_o = 1'b1;
            		rresp_o = 2'b00; // (OKAY)

            if (rready_i) begin
                //Check for valid address
                if (araddr_i != 32'h00000000 && araddr_i != 32'h00000004 && araddr_i != 32'h00000008 && araddr_i != 32'h0000000C || arvalid_i == 1'b0) begin
                    rresp_o = 2'b10; // (SLVERR)
                end
                //Check for valid data
                else if (rdata_o > 32'hFFFFFFFF) begin
                    rresp_o = 2'b10; // (SLVERR)
                end
                //If both address and data are valid, perform the write
                else begin
                    if (araddr_i == 32'h00000000) rdata_o = register[0];
                    else if (araddr_i == 32'h00000004) rdata_o = register[1];
                    else if (araddr_i == 32'h00000008) rdata_o = register[2];
                    else if (araddr_i == 32'h0000000C) rdata_o = register[3];
                    rresp_o = 2'b00; // (OKAY)
                end
            end
		
	    else begin
		rresp_o = 2'b10;
	    end
        end

	//If address is invalid 
        if (!arvalid_i) begin
            arready_o = 1'b0;
            rresp_o = 2'b10; // (SLVERR)
        end

	end
end


endmodule
