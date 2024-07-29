import cache_defs::*;

module tb_cache_controller#(parameter DATA_WIDTH = 32);

logic clk;
logic reset;

logic flush;
logic [DATA_WIDTH-1:0]address;
logic [DATA_WIDTH-1:0]data_in;
logic main_mem_ack;

logic hit;
logic miss;
logic [DATA_WIDTH-1:0]data_out;

logic read_done;
logic write_done;

logic busy;


CPU_Request_type cpu_request;


cache_controller CACHE_CONTROLLER(

.clk(clk),
.reset(reset),
.flush(flush),
.address(address),
.data_in(data_in),
.main_mem_ack(main_mem_ack),
.cpu_request(cpu_request),

.hit(hit),
.miss(miss),
.data_out(data_out),
.read_done(read_done),
.write_done(write_done),
.busy(busy)


);







initial begin
   clk = 0;
   forever #20 clk = ~clk;
end






task initialization();

cpu_request.write = 1'b0;
cpu_request.read = 1'b0;
data_in = 0;
main_mem_ack = 0;

endtask


//Test case 1
task check_read_hit_miss();

  //Read Miss and Read Hit testing
  cpu_request.write = 1'b1;
  address = 32'h0000_0002;
  data_in = 32'hFFFF_FFFF;
  main_mem_ack = 1'b0;

  @(posedge clk);
  main_mem_ack = 1'b1;

  @(posedge clk);
  wait(miss) $display("Data not dound in cache , it's a read miss");

  @(posedge clk);

  wait(hit) begin
       main_mem_ack = 1'b0;
  end

  

  @(posedge clk);
  cpu_request.read = 1'b1;
  address = 32'h0000_0002;
  wait(read_done) begin
      if(data_out == data_in) $display("Data found in the cache , it's a read hit");
      else $display("Data not found in the cache , it's a read miss");
  end

 
  @(posedge clk);
  cpu_request.write = 1'b0;
  wait(data_out == data_in) cpu_request.read = 1'b0;
  


endtask


//Test case 2
task check_write_miss();

// Write Miss testing
cpu_request.write = 1'b1;
address = 32'h0000_0004;
data_in = 32'hFFFF_FFFF;
main_mem_ack = 1'b0;

@(posedge clk);
main_mem_ack = 1'b1;

wait(miss) begin
      main_mem_ack = 1'b0;
      $display("Cache line is not valid, it's a write miss");
end

@(posedge clk);
cpu_request.write = 1'b0;

endtask




//Test case 3
task check_write_hit();

    // Write Hit testing
    cpu_request.write = 1'b1;
    address = 32'h0000_0002;
    data_in = 32'hAAAA_AAAA;
    main_mem_ack = 1'b0;

    @(posedge clk);
    main_mem_ack = 1'b1;

    wait(hit) begin
        main_mem_ack = 1'b0;
        $display("Data found in the cache, it's a write hit");
    end

    @(posedge clk);
    cpu_request.write = 1'b0;
endtask


//write operation
task data_write(logic [DATA_WIDTH-1:0]data);

    cpu_request.write = 1'b1;
    address = 32'h0000_0002;
    data_in = data;
    main_mem_ack = 1'b1;

endtask



//reset
task reset_cache();
    reset = 1;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    reset = 0;
endtask






initial begin

  initialization();

  reset_cache();

  //check_read_hit_miss();
  //@(posedge clk);
  //@(posedge clk);
  //check_write_hit();
  //@(posedge clk);
  check_write_miss();



end


endmodule
