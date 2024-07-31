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
logic [128-1:0]data_out;

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
  address = 32'h0000_0003;
  data_in = 32'hFAFA_ADAD;
  main_mem_ack = 1'b0;

  @(posedge clk);
  main_mem_ack = 1'b1;

  @(posedge clk);
  wait(miss) $display("[1]TEST PASSED (READ MISS)");

  @(posedge clk);

  wait(hit) begin
       main_mem_ack = 1'b0;
  end

  

  @(posedge clk);
  cpu_request.read = 1'b1;
  address = 32'h0000_0003;
  wait(read_done) begin
      if(data_out == data_in) $display("[2]TEST PASSED (READ HIT)");
      else $display("Error : Data not found in the cache , it's a read miss");
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
      $display("[4]TEST PASSED (WRITE MISS)");
end

@(posedge clk);
cpu_request.write = 1'b0;

endtask




//Test case 3
task check_write_hit();

    // Write Hit testing
    cpu_request.write = 1'b1;
    address = 32'h0000_0032;
    data_in = 32'hFFFF_FFFF;
    main_mem_ack = 1'b0;

    @(posedge clk);
    main_mem_ack = 1'b1;

    wait(hit) begin
        main_mem_ack = 1'b0;
        $display("[3]TEST PASSED (WRITE HIT)");
    end

    @(posedge clk);
    cpu_request.write = 1'b0;
endtask




//reset
task reset_cache();
    reset = 1;
    #50
    reset = 0;
endtask








initial begin

  initialization();

  reset_cache();


  check_write_hit();

  //check_read_hit_miss();

 //check_write_miss();

  //$display("ALL TEST PASSED SUCCESSFULLY");

end


endmodule


