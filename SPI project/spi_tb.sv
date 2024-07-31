`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/15/2024 12:58:38 AM
// Design Name: 
// Module Name: spi_tb
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
module spi_master_tb;

    // Parameters
    //parameter CLK_PERIOD = 10; // Clock period in ns
    
    // Signals
    logic clk;
    logic rst_n;
    logic start_transaction;
    logic [7:0] tx_data;
    logic [7:0] rx_data;
    logic transaction_done;
    logic sclk;
    logic mosi;
    logic miso;
    logic ss_n;

    // Instantiate SPI Master module
    spi_master dut (
        .clk(clk),
        .rst_n(rst_n),
        .start_transaction(start_transaction),
        .tx_data(tx_data),
        .rx_data(rx_data),
        .transaction_done(transaction_done),
        .sclk(sclk),
        .mosi(mosi),
        .miso(miso),
        .ss_n(ss_n)
    );

    // Clock generation process
    initial begin
    clk=0;
    forever #5 clk = ~clk;
    end
    

    // Initial stimulus
    initial begin
        // Initialize inputs
        rst_n = 1;
        start_transaction = 0;
        tx_data = 8'h00;
        miso = 0;

        // Reset
        @(posedge clk);
        rst_n = 0;

        // Test case 1: Single transaction
        @(posedge clk);
        start_transaction = 1;
        tx_data = 8'hAA; // Example data to transmit

        // Wait for transaction to complete
        repeat (10) @(posedge clk);

        // Test case 2: Multiple transactions
        start_transaction = 1;
        tx_data = 8'h55; // Example data to transmit

        repeat (20) @(posedge clk);

        // End simulation

        $finish;
    end

endmodule

