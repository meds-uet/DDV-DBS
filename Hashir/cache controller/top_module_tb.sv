`timescale 1ns / 1ps

module top_module_tb;

    logic clk, reset, CPU_request, read_req, write_req;
    logic [31:0] address, data_in, data_out;
    integer i;

    top_module uut (
        .clk(clk),
        .reset(reset),
        .CPU_request(CPU_request),
        .address(address),
        .data_in(data_in),
        .read_req(read_req),
        .write_req(write_req),
        .data_out(data_out)
    );

    always #5 clk = ~clk;

    initial begin
        clk = 0;
        reset = 0;
        CPU_request = 0;
        read_req = 0;
        write_req = 0;
        address = 32'h0;
        data_in = 32'h0;

        #10 reset = 1;
        
        #100;

        for (i = 0; i < 8; i++) begin
            #10 CPU_request = 1; write_req = 1; address = i * 4; data_in = i;
            #10 CPU_request = 0; write_req = 0;
        end

        for (i = 0; i < 8; i++) begin
            #10 CPU_request = 1; read_req = 1; address = i * 4;
            #10 CPU_request = 0; read_req = 0;
        end

        for (i = 0; i < 8; i++) begin
            #10 CPU_request = 1; write_req = 1; address = i * 4; data_in = i;
            #10 CPU_request = 0; write_req = 0;
        end

        #10 CPU_request = 1; read_req = 1; address = 32'h100;
        #10 CPU_request = 0; read_req = 0;

        #100 $finish;
    end

    initial begin
        $monitor("Time: %0t, Address: %h, Data Out: %h", $time, address, data_out);
    end

endmodule
