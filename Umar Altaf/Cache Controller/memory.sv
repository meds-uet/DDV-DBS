`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/24/2024 12:51:31 PM
// Design Name: 
// Module Name: memory
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


module memory(
    input logic clk,
    input logic rst_n,
    input logic mem_write,
    input logic mem_read,
    input logic [31:0] m_addr,
    input logic [127:0] m_w_data,
    output logic [127:0] m_r_data,
    output logic main_mem_ack
);

    // Memory definition (512 sets, each holding 128 bits)
    logic [127:0] memory [0:511];

    always_ff @(posedge clk or negedge rst_n) begin
        if (rst_n) begin
            // Initialize memory 
            for(int j=0;j<512;j++)
              begin
              memory[j]<=128'h00ab_cd00_00ef_1200_0034_5600_0078_9a00+(j*4'hf);
              
                           end
        end else begin
            if (mem_write) begin
                memory[m_addr[8:0]] <= m_w_data;
                main_mem_ack <= 1;
            end else if (mem_read) begin
                m_r_data <= memory[m_addr[8:0]];
                main_mem_ack <= 1;
            end else begin
                main_mem_ack <= 0;
            end
        end
    end

endmodule

