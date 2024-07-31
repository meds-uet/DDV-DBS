// Define an interface for the FIFO
interface fifo_if;
  
  logic clock, rd, wr;         // Clock, read, and write signals
  logic full, empty;           // Flags indicating FIFO status
  logic [7:0] data_in;         // Data input
  logic [7:0] data_out;        // Data output
  logic rst;                   // Reset signal
 
endinterface