module tb_axi_lite_slave;

   
    localparam CLK_PERIOD = 10; 

    
    logic        aclk;    // Clock signal
    logic        aresetn; // Active-low reset signal

    
    logic [31:0] araddr;  // Read address
    logic        arvalid; // Read address valid
    logic        arready; // Read address ready

   
    logic [31:0] rdata;   // Read data
    logic [1:0]  rresp;   // Read response
    logic        rvalid;  // Read valid
    logic        rready;  // Read ready

   
    logic [31:0] awaddr;  // Write address
    logic        awvalid; // Write address valid
    logic        awready; // Write address ready

 
    logic [31:0] wdata;   // Write data
    logic [3:0]  wstrb;   // Write strobe
    logic        wvalid;  // Write valid
    logic        wready;  // Write ready

 
    logic [1:0]  bresp;   // Write response
    logic        bvalid;  // Write response valid
    logic        bready;  // Write response ready

    
    axi_lite_slave DUT (
        .aclk(aclk),
        .aresetn(aresetn),
        .araddr(araddr),
        .arvalid(arvalid),
        .arready(arready),
        .rdata(rdata),
        .rresp(rresp),
        .rvalid(rvalid),
        .rready(rready),
        .awaddr(awaddr),
        .awvalid(awvalid),
        .awready(awready),
        .wdata(wdata),
        .wstrb(wstrb),
        .wvalid(wvalid),
        .wready(wready),
        .bresp(bresp),
        .bvalid(bvalid),
        .bready(bready)
    );

   
    initial begin
        aclk = 0;
        forever #(CLK_PERIOD/2) aclk = ~aclk; 
    end

  
    initial begin
        
        aresetn = 0;
        araddr = 0;
        arvalid = 0;
        rready = 0;
        awaddr = 0;
        awvalid = 0;
        wdata = 0;
        wstrb = 4'b1111; 
        wvalid = 0;
        bready = 0;

       
        #(CLK_PERIOD * 5); // Delay for 5 cycles
        aresetn = 1;       
        #(CLK_PERIOD * 2); // Delay for 2 cycles

       
        write_transaction(32'h0000, 32'hA5A5A5A5);

       
        read_transaction(32'h0000);

      
        write_transaction(32'h0008, 32'h12345678);

      
        read_transaction(32'h0008);

        
        write_transaction(32'h1000, 32'hDEADBEEF);

   
        read_transaction(32'h1000);

       
        #(CLK_PERIOD * 10);
        $finish;
    end

  
    task write_transaction(input [31:0] addr, input [31:0] data);
        begin
            awaddr = addr;
            awvalid = 1;
            wdata = data;
            wvalid = 1;
            bready = 1;
            wait(awready && wready); 
            awvalid = 0;
            wvalid = 0;
            wait(bvalid); 
            if (bresp == 2'b00) begin
                $display("Write to address %h successful, data: %h", addr, data);
            end else begin
                $display("Write to address %h failed, response: %b", addr, bresp);
            end
            bready = 0;
        end
    endtask

    
    task read_transaction(input [31:0] addr);
        begin
            araddr = addr;
            arvalid = 1;
            rready = 1;
            wait(arready); 
            arvalid = 0;
            wait(rvalid); 
            if (rresp == 2'b00) begin
                $display("Read from address %h successful, data: %h", addr, rdata);
            end else begin
                $display("Read from address %h failed, response: %b", addr, rresp);
            end
            rready = 0;
        end
    endtask

 
    initial begin
        forever begin
            @(posedge aclk);
            if (awvalid && awready)
                $display("Write Address: %h", awaddr);
            if (wvalid && wready)
                $display("Write Data: %h", wdata);
            if (bvalid && bready)
                $display("Write Response: %h", bresp);
            if (arvalid && arready)
                $display("Read Address: %h", araddr);
            if (rvalid && rready)
                $display("Read Data: %h, Response: %h", rdata, rresp);
        end
    end