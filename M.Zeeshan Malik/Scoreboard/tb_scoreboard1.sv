`include "scoreboard.sv"

module tb_dut;
    // DUT signals
    logic clk, reset;
    logic [7:0] data_in, data_out;
    logic [7:0] A, B;
    logic [2:0] op;
    logic [7:0] result;
    logic fifo_write_en, fifo_read_en;
    logic fifo_full, fifo_empty;
    logic read_complete;

    // Instantiate DUT
    ALU_ref uut_ALU_ref (
        .A(A),
        .B(B),
        .op(op),
        .result_expected(result)
    );

    // Instantiate FIFO
    FIFO #(.WIDTH(8), .DEPTH(8)) fifo (
        .clk(clk),
        .reset(reset),
        .data_in(result),
        .wr_en(fifo_write_en),
        .rd_en(fifo_read_en),
        .data_out(data_out),
        .full(fifo_full),
        .empty(fifo_empty)
    );

    // Instantiate Scoreboard
    Scoreboard #(.DATA_WIDTH(8)) scoreboard;

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Test stimulus and scoreboard usage
    initial begin
        // Initialize
        scoreboard = new();
        reset = 1;
        data_in = 8'h00;
        fifo_write_en = 0;
        fifo_read_en = 0;
        read_complete = 0;
        @(posedge clk);
        reset = 0;

        // Test case 1: Simple addition
        A = 8'h01; B = 8'h01; op = 3'b000;
        #10;
        fifo_write_en = 1;
        @(posedge clk);
        fifo_write_en = 0;
        #10 scoreboard.add_expected(8'h02);

        // Test case 2: Simple subtraction
        A = 8'h02; B = 8'h01; op = 3'b001;
        #10;
        fifo_write_en = 1;
        @(posedge clk);
        fifo_write_en = 0;
        #10 scoreboard.add_expected(8'h01);

        // Test case 3: Simple AND
        A = 8'hFF; B = 8'h0F; op = 3'b010;
        #10;
        fifo_write_en = 1;
        @(posedge clk);
        fifo_write_en = 0;
        #10 scoreboard.add_expected(8'h0A);

        // Test case 4: Simple addition
        A = 8'h01; B = 8'h01; op = 3'b000;
        #10;
        fifo_write_en = 1;
        @(posedge clk);
        fifo_write_en = 0;
        #10 scoreboard.add_expected(8'h02);

        // Test case 5: Simple subtraction
        A = 8'h02; B = 8'h01; op = 3'b001;
        #10;
        fifo_write_en = 1;
        @(posedge clk);
        fifo_write_en = 0;
        #10 scoreboard.add_expected(8'h04);

        // Reading from FIFO and comparing results
        //for (int i = 0; i < 3; i++) begin // Adjust the loop count based on the number of test cases
        while(!fifo_empty) begin
            @(posedge clk);
            fifo_read_en = 1;
            @(posedge clk);
            fifo_read_en = 0;
            @(posedge clk);
            #10 scoreboard.compare_result(data_out);
        end

        // Report scoreboard statistics
        scoreboard.report_statistics();

        $finish;
    end
endmodule
