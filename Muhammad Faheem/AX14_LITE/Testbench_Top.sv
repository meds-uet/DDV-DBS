`timescale 1ns / 1ps

module AXI4_tb;



    // AXI4-Lite interface signals
    logic        aclk;    // Clock signal
    logic        aresetn; // Active-low reset signal

    // Read address channel
    logic [31:0] araddr;  // Read address
    logic        arvalid; // Read address valid
    logic        arready; // Read address ready

    // Read data channel
    logic [31:0] rdata;   // Read data
    logic [1:0]  rresp;   // Read response
    logic        rvalid;  // Read valid
    logic        rready;  // Read ready

    // Write address channel
    logic [31:0] awaddr;  // Write address
    logic        awvalid; // Write address valid
    logic        awready; // Write address ready

    // Write data channel
    logic [31:0] wdata;   // Write data
    logic [3:0]  wstrb;   // Write strobe
    logic        wvalid;  // Write valid
    logic        wready;  // Write ready

    // Write response channel
    logic [1:0]  bresp;   // Write response
    logic        bvalid;  // Write response valid
    logic        bready;  // Write response ready

    // Instantiate the Unit Under Test (UUT)
    AXI4_Lite uut (
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

    // Clock generation
    initial begin
        aclk = 0;
        forever #5 aclk = ~aclk;
    end

    // Test stimulus
    initial begin
        // Initialize all signals
        araddr = 0;
        arvalid = 0;
        rready = 0;
        awaddr = 0;
        awvalid = 0;
        wdata = 0;
        wstrb = 4'b1111;
        wvalid = 0;
        bready = 0;
        end
       
initial begin
  //reset the dut at start  
  reset();
  //write operation with valid address
  write_transaction(32'h00000004,32'hdeadbeef);
  #20
  //read operation with valid address
  read_transaction(32'h00000004);
  #20
  //write operation with valid address
  write_transaction(32'h00000008,32'haaaaffff);
  #20
  //read operation with valid address
  read_transaction(32'h00000008);
  #20
  //write operation with invalid address
  write_transaction(32'h00000002,32'hbeefcafe);
  #20
  //read operation with invalid address
  read_transaction(32'h0000000f);
  
end
  
 initial begin    
   // VCD file generation
   $dumpfile("axi4_lite_tb.vcd");
   $dumpvars(0, AXI4_tb);
   // End simulation
   #500;
   $finish;    
    end

    // Task for write transaction
    task write_transaction(input [31:0] addr, input [31:0] data);
        begin
            // Issue write address and data
          @(posedge aclk);
          if(awready) begin
            awvalid = 1;
            awaddr = addr;
          end
          else
            awvalid = 0;
          wait(wready);
           awvalid = 0;
          @(posedge aclk);
          if(wready) begin
            wvalid = 1;
            wdata = data; 
          end
          else
            wvalid = 0; 
          @(posedge aclk);
           wvalid = 0;           
        end
    endtask
  
  
  task reset;
    begin
         // Reset sequence
        aresetn = 1;
        #20
        aresetn = 0;
        #20;
    end
  endtask

    // Task for read transaction
    task read_transaction(input [31:0] addr);
        begin
         @(posedge aclk);
          if(arready) begin
            arvalid = 1;
            araddr = addr;
          end
          else
            arvalid = 0;
          wait(rvalid);
           arvalid = 0;
          @(posedge aclk);
          if(rvalid)
            rready = 1;
          else
            rready = 0; 
          @(posedge aclk);
           rready = 0; 
        end
    endtask

    // Monitor process to display transactions
    initial begin
        forever begin
            @(posedge aclk);
            if (awvalid && awready)
                $display("Write Address: %h", awaddr);
            if (wvalid && wready)
                $display("Write Data: %h", wdata);
            if (bvalid)
                $display("Write Response: %h", bresp);
            if (arvalid && arready)
                $display("Read Address: %h", araddr);
            if (rvalid && rready)
                $display("Read Data: %h, Response: %h", rdata, rresp);
        end
    end

endmodule