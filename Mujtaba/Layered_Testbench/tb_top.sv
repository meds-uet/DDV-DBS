`include "transaction.sv"
`include "test.sv"

module tb_top;

  // Instantiate the design interface and pass the signals to it
  design_interface _if();

  // Instantiate the test module and pass the interface
  test test1(_if);

  // Instantiate the DUT (FIFO in this case) and connect it to the interface
  dut BCD_TO_7SEGMENT_DECODER(
    .in(_if.in),
    .binary_code(_if.binary_code)
  );


 
endmodule

