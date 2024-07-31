`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/19/2024 11:00:14 AM
// Design Name: 
// Module Name: tb_cache_contoller
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


`include "memory.sv"
module tb_cache_controller;
  // Declare signals
  logic clk;
  logic rst_n;
  logic read_req;
  logic write_req;
  logic cache_flush;
  logic [31:0] p_addr;
  logic [31:0] m_addr;
  logic [31:0] p_w_data;
  logic [31:0] p_r_data;
  logic [127:0] m_r_data;
  logic [127:0] m_w_data;
  logic main_mem_ack;
  logic mem_write;
  logic mem_read;
  logic stall;

  // Instantiate the cache controller
  cache_controller uut (
    .clk(clk),
    .rst_n(rst_n),
    .read_req(read_req),
    .write_req(write_req),
    .cache_flush(cache_flush),
    .p_addr(p_addr),
    .m_addr(m_addr),
    .p_w_data(p_w_data),
    .p_r_data(p_r_data),
    .m_r_data(m_r_data),
    .m_w_data(m_w_data),
    .main_mem_ack(main_mem_ack),
    .mem_write(mem_write),
    .mem_read(mem_read),
    .stall(stall)
  );
memory mm(
    .clk(clk),
    .rst_n(rst_n),
    .mem_write(mem_write),
    .mem_read(mem_read),
    .m_addr(m_addr),
    .m_w_data(m_w_data),
    .m_r_data(m_r_data),
    .main_mem_ack(main_mem_ack)
  );

 
  // Generate clock
    initial begin
      clk = 0;
      forever #5 clk = ~clk; // 100MHz clock (10ns period)
    end

  // Reset sequence
  initial begin
    rst_n = 1;
    @(posedge clk);
     @(posedge clk);
    rst_n = 0;
 write_req=0;
 read_req=0;
 cache_flush=0;

  
    // Initialize inputs
//    read_req <= 0;
//    write_req <= 0;
//    cache_flush<= 0;
//    p_addr <= 32'h0000_0000;
//    p_w_data <= 32'h0000_0000;
//    m_r_data <= 0;
//       main_mem_ack <= 0;
 @(posedge clk);
          @(posedge clk);
          
 for (int k=0;k<5;k++)//writing on 5 locations of cache making dirty bit high
 //also index 0 write is tested
begin
    // Example stimulus


    // Test write request
    
    write_req = 1;
    p_addr = 32'hABCD_0000+(k*(8'h10));
    p_w_data = 32'hABCD_EF01;   
//     @(posedge clk);
//       @(posedge clk);
       
//    main_mem_ack = 1;
     @(posedge clk);
     @(posedge clk);
     write_req=0 ;
     
      @(posedge clk);
      @(posedge clk);
      @(posedge clk);
      @(posedge clk);
      @(posedge clk);
      @(posedge clk);
      @(posedge clk);
      @(posedge clk);
      @(posedge clk);
         

 end  
     @(posedge clk);
                               read_req = 1;// invalid address
                               p_addr = 32'hABCD_ff01;
                               p_w_data = 32'hABCD_EF01;  
                               @(posedge clk);
                               @(posedge clk);
                               read_req=0 ;                                                                 
                                @(posedge clk);
                                   @(posedge clk);
                                   @(posedge clk);
                                   @(posedge clk);
                                   @(posedge clk);
                                   @(posedge clk);
                                   @(posedge clk);
                                   @(posedge clk);
                                   @(posedge clk);
                                   
  @(posedge clk);
   for (int k=0;k<2;k++)
   begin
                               write_req = 1;// checking same address multiple calls 
                               p_addr = 32'hABCD_0000;
                               p_w_data = 32'hABCD_EF01;  
                               @(posedge clk);
                               @(posedge clk);
                               write_req=0 ;                                                                 
                              @(posedge clk);
                                   @(posedge clk);
                                   @(posedge clk);
                                   @(posedge clk);
                                   @(posedge clk);
                                   @(posedge clk);
                                   @(posedge clk);
                                   @(posedge clk);
                                   @(posedge clk);                                              
end
                             write_req = 1;// write at index 255
                             p_addr = 32'hABCD_0ff0;
                             p_w_data = 32'hABCD_EF01;  
                             @(posedge clk);
                             @(posedge clk);
                             write_req=0 ;                                                                 
                             @(posedge clk);
                             @(posedge clk);
                             @(posedge clk);
                             @(posedge clk);
                             @(posedge clk);
                             @(posedge clk);
                             @(posedge clk);
                             @(posedge clk);
                             @(posedge clk);   
                                                                                                     

                              
                                                 
  @(posedge clk);
                            read_req = 1;// checkng read hit
                            p_addr = 32'h2af3_4000;
                            p_w_data = 32'hABCD_EF01;  
                            @(posedge clk);
                            @(posedge clk);
                            read_req=0 ;                                                                 
                            @(posedge clk);
                              @(posedge clk);                                                         
                                 @(posedge clk);
                                                         @(posedge clk);
                                                         @(posedge clk);
                                                         @(posedge clk);
                                                         @(posedge clk);
                                                         @(posedge clk);
                                                         @(posedge clk);
                                                         @(posedge clk);                         
                                                        
//cache_flush=1;
// @(posedge clk);
//         @(posedge clk);
//                @(posedge clk);
//              @(posedge clk);
//              @(posedge clk);
//                   @(posedge clk);
//                     @(posedge clk);
//                                @(posedge clk);
//                                     @(posedge clk);
    // End of simulation
    repeat (500) @(posedge clk);
      
    $finish;
  end

  // Monitor outputs
//  initial begin
//    $monitor("Time: %0t | clk: %b | rst_n: %b | read_req: %b | write_req: %b | cache_flush: %b | p_addr: %h | p_w_data: %h | m_r_data: %h | m_addr: %h | p_r_data: %h | m_w_data: %h | main_mem_ack: %b | mem_write: %b | mem_read: %b | stall: %b", 
//             $time, clk, rst_n, read_req, write_req, cache_flush, p_addr, p_w_data, m_r_data, m_addr, p_r_data, m_w_data, main_mem_ack, mem_write, mem_read, stall);
//  end

endmodule




