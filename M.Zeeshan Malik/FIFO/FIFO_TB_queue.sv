module fifo_tb;
    // Parameters
    parameter WIDTH = 16;
    parameter DEPTH = 8;

    // Signals
    logic clk;
    logic reset;
    logic [WIDTH-1:0] data_in;
    logic wr_en;
    logic rd_en;
    logic [WIDTH-1:0] data_out;
    logic full;
    logic empty;

    // FIFO instance
    FIFO #(
        .WIDTH(WIDTH),
        .DEPTH(DEPTH)
    ) fifo_inst (
        .clk(clk),
        .reset(reset),
        .data_in(data_in),
        .wr_en(wr_en),
        .rd_en(rd_en),
        .data_out(data_out),
        .full(full),
        .empty(empty)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns clock period
    end

    // Test procedure
    initial begin
        // Initialize signals
        reset = 1;
        data_in = 0;
        wr_en = 0;
        rd_en = 0;

        // Release reset
        #10 reset = 0;

        // Test writing to the FIFO
        $display("Starting FIFO Write Test");
        write_fifo(16'hAAAA);
        write_fifo(16'hBBBB);
        write_fifo(16'hCCCC);
        write_fifo(16'hDDDD);
        write_fifo(16'hEEEE);
        write_fifo(16'hFFFF);
        write_fifo(16'h1234);
        write_fifo(16'h5678);

        // Attempt to write to a full FIFO (should not write)
        wr_en = 1;
        data_in = 16'h9ABC;
        @(posedge clk);
        if (full) $display("FIFO is full as expected");
        wr_en = 0;

        // Test reading from the FIFO
        $display("Starting FIFO Read Test");
        read_fifo(16'hAAAA);
        read_fifo(16'hBBBB);
        read_fifo(16'hCCCC);
        read_fifo(16'hDDDD);
        read_fifo(16'hEEEE);
        read_fifo(16'hFFFF);
        read_fifo(16'h1234);
        read_fifo(16'h5678);

        // Attempt to read from an empty FIFO (should not read)
        rd_en = 1;
        @(posedge clk);
        if (empty) $display("FIFO is empty as expected");
        rd_en = 0;

        // Finish simulation
        $finish;
    end

    // Task to write data to the FIFO
    task write_fifo(input logic [WIDTH-1:0] data);
        begin
            @(posedge clk);
            if (!full) begin
                data_in = data;
                wr_en = 1;
                @(posedge clk);
                wr_en = 0;
                $display("Wrote data: %h", data);
            end else begin
                $display("ERROR: FIFO is full, cannot write data: %h", data);
            end
        end
    endtask

    // Task to read data from the FIFO
    task read_fifo(input logic [WIDTH-1:0] expected_data);
        begin
            @(posedge clk);
            if (!empty) begin
                rd_en = 1;
                @(posedge clk);
                rd_en = 0;
                if (data_out !== expected_data) begin
                    $display("ERROR: Read data %h does not match expected data %h", data_out, expected_data);
                end else begin
                    $display("Read data: %h", data_out);
                end
            end else begin
                $display("ERROR: FIFO is empty, cannot read data");
            end
        end
    endtask

endmodule
