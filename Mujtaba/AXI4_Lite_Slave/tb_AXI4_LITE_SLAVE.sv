module tb_AXI4_LITE_SLAVE#(parameter ADDR_WIDTH = 32,
                           parameter DATA_WIDTH = 32);



//Interface handle
slave_interface _if();




AXI4_LITE_SLAVE SLAVE(


.clk(_if.clk),
.reset(_if.reset),

//Write Address Channel
.awaddr_i(_if.awaddr_i),
.awvalid_i(_if.awvalid_i),

//Write Data Channel
.wdata_i(_if.wdata_i),
.wvalid_i(_if.wvalid_i),


//Write response channel
.bready_i(_if.bready_i),
                                    


//Read address channel
.araddr_i(_if.araddr_i),
.arvalid_i(_if.arvalid_i),


//Read data channel
.rready_i(_if.rready_i),



/** -------------OUTPUTS-------------------- **/

//Write Address Channel
.awready_o(_if.awready_o),

//Write Data Channel
.wready_o(_if.wready_o),


//Write response channel
.bresp_o(_if.bresp_o),

.bvalid_o(_if.bvalid_o),


//Read address channel
.arready_o(_if.arready_o),


//Read data channel
.rdata_o(_if.rdata_o),//read data
.rresp_o(_if.rresp_o),

.rvalid_o(_if.rvalid_o)

);


initial begin
	_if.clk = 0;
	forever #20 _if.clk = ~_if.clk;
end



initial begin
	_if.reset = 1;
	#20
	_if.reset = 0;
end


initial begin
	_if.awvalid_i = 0;
	_if.bready_i = 0;
	_if.wvalid_i = 0;
end





initial begin

	//Write transaction

	//@(posedge _if.clk);
	//Test case 1 : Write without errors
	_if.awvalid_i = 1;
	_if.bready_i = 1;
	_if.wvalid_i = 1;
	_if.awaddr_i = 32'h00000000;
	_if.wdata_i = 32'h12345678;


	//Test case 2 : Writing invalid address	
	#40
	//@(posedge _if.clk);
	_if.awvalid_i = 0;
	_if.bready_i = 1;
	_if.wvalid_i = 1;
	_if.awaddr_i = 32'h00000010;
	_if.wdata_i = 32'h00000002;

	#40

	//Test case 3 : Writing invalid data
	//@(posedge _if.clk);
	_if.awvalid_i = 1;
	_if.bready_i = 1;
	_if.wvalid_i = 0;
	_if.awaddr_i = 32'h00000004;
	_if.wdata_i = 40'h765ABCD47A;

	//Test case 4: Again doing valid write transaction
	#40
	//@(posedge _if.clk);
	_if.awvalid_i = 1;
	_if.bready_i = 1;
	_if.wvalid_i = 1;
	_if.awaddr_i = 32'h0000000C;
	_if.wdata_i = 32'hFFFFFFFF;

	//Test case 5 : Busy
	#40
	//@(posedge _if.clk);
	_if.awvalid_i = 1;
	_if.bready_i = 0;
	_if.wvalid_i = 1;
	_if.awaddr_i = 32'h00000000;
	_if.wdata_i = 32'hBCD56900;

	//Test case 6 : Again doing valid write transaction
	#40
	//@(posedge _if.clk);
	_if.awvalid_i = 1;
	_if.bready_i = 1;
	_if.wvalid_i = 1;
	_if.awaddr_i = 32'h00000004;
	_if.wdata_i = 32'hBCDF1278;


	//Test case 7 : Checking data integrity 
	#40
	_if.arvalid_i = 1;
	_if.rready_i = 1;
	_if.araddr_i = 32'h00000000;

	
	//Test case 8 : read on invalid address
	#40
	_if.arvalid_i = 0;
	_if.rready_i = 1;
	_if.araddr_i = 32'h00000009;


	//Test case 9 : master not ready to accept read data
	#40
	_if.arvalid_i = 1;
	_if.rready_i = 0;
	_if.araddr_i = 32'h00000004;


	//Test case 10 : doing a valid read transaction again
	#40
	_if.arvalid_i = 1;
	_if.rready_i = 1;
	_if.araddr_i = 32'h00000004;
	
	

end


endmodule
