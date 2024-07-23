module serial_to_parallel_tb;
    // Parameters
    parameter WIDTH = 8;
    
    // Signals
    logic clk;
    logic rst_n;
    logic serial_in;
    logic msb_first;
    logic [WIDTH-1:0] parallel_out;
    logic [WIDTH-1:0] expected_parallel_out;
    logic data_valid;

    // DUT instantiation
    serial_to_parallel #(
        .WIDTH(WIDTH)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .serial_in(serial_in),
        .msb_first(msb_first),
        .parallel_out(parallel_out),
        .data_valid(data_valid)
    );

    // Clock generation
    always #5 clk = ~clk;

    // Test stimulus and checking
    initial begin
        // : Initializing signals
        clk = 1;
        rst_n = 0;
        serial_in = 0;
        msb_first = 0;
        #5;
        rst_n = 1;
        for (msb_first = 0; msb_first < 2; msb_first++) begin
            for (int i = 0; i< WIDTH; i++)begin
                if (msb_first == 1'b0)
                    task_lsb_first(i,msb_first); //task to verify lsb first
                else
                    task_msb_first(i,msb_first); //task to verify msb first
            end
            end
        end

    task task_lsb_first(input int test_num, input logic msb_first);
         begin
            repeat(32)@(posedge clk)serial_in = $urandom;
         end
         #400;
    endtask

    task task_msb_first(input int test_num, input logic msb_first);
         begin
            repeat(32)@(posedge clk)serial_in = $urandom;
         end
         #410;
         $finish;
    endtask

    initial begin
        $dumpfile("mid.vcd");
        $dumpvars(0,"serial_to_parallel_tb");
    end

endmodule
