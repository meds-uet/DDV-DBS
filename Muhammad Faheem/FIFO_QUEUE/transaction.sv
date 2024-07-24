class transaction;
  
  rand bit oper;          // Randomized bit for operation control (1 or 0)
  bit rd, wr;             // Read and write control bits
  bit [7:0] data_in;      // 8-bit data input
  bit full, empty;        // Flags for full and empty status
  bit [7:0] data_out;     // 8-bit data output
  
  constraint oper_ctrl {  
    oper dist {1 :/ 50 , 0 :/ 50};  // Constraint to randomize 'oper' with 50% probability of 1 and 50% probability of 0
  }
  
endclass