module FIFO #(
  parameter Width = 8,
  parameter Depth = 16,
  parameter PtrWidth = $clog2(Width)
) (
  input logic clk,
  input logic reset,
  input logic write_en,
  input logic read_en,
  input logic [Width-1:0] data_in,
  output logic [Width-1:0] data_out,
  output logic full,
  output logic empty
);
reg[Width-1:0]mem[Depth];
reg[PtrWidth:0] rdPtr,rdPtrNext;
reg[PtrWidth:0] wrPtr,wrPtrNext;

always_comb begin
    wrPtrNext = wrPtr;
    rdPtrNext = rdPtr;
    if(write_en)begin 
    wrPtrNext = wrPtr + 1;  
    end
    if(read_en)begin 
    rdPtrNext = rdPtr + 1;  
    end
 end
 
 always_ff@(posedge clk or posedge reset)begin
 if(!reset)begin 
    wrPtr <= 0;
    rdPtr <= 0;
 end 
 else begin
     wrPtr = wrPtrNext;
     rdPtr = rdPtrNext; 
 end
  mem[wrPtr[PtrWidth-1:0]] <= data_in;
 
 end
 
 assign  data_out = mem[rdPtr[PtrWidth-1:0]];
 
 assign empty = (wrPtr[PtrWidth] == rdPtr[PtrWidth]) && (wrPtr[PtrWidth-1:0]) == rdPtr[PtrWidth-1:0]; 
 assign full = (wrPtr[PtrWidth] != rdPtr[PtrWidth]) && (wrPtr[PtrWidth-1:0]) == rdPtr[PtrWidth-1:0];
endmodule
