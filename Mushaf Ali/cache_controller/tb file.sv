module tope_module_tb;

  // Declare inputs as regs and outputs as wires
  reg clk;
  reg rst;
  reg [31:0] address;
  reg [31:0] pr_write_data_in;
  wire [31:0] pr_read_data;
  wire [3:0][31:0] data_out_mem;
  reg [3:0][31:0] data_in_mem;
  reg read_in;
  reg write_in;
  reg read_ack;
  reg write_ack;

  // Instantiate the Unit Under Test (UUT)
  tope_module uut (
    .clk(clk),
    .rst(rst),
    .address(address),
    .pr_write_data_in(pr_write_data_in),
    .pr_read_data(pr_read_data),
    .data_out_mem(data_out_mem),
    .data_in_mem(data_in_mem),
    .read_in(read_in),
    .write_in(write_in),
    .read_ack(read_ack),
    .write_ack(write_ack)
  );

  // Clock generation
  always #5 clk = ~clk; // 10 ns clock period

  initial begin
    // Initialize Inputs
    clk = 0;
    rst = 0;
    address = 0;
    pr_write_data_in = 0;
    data_in_mem = 0;
    read_in = 0;
    write_in = 0;
    read_ack = 0;
    write_ack = 0;

    // Apply reset
    rst = 1;
    #10;
    rst = 0;

    // Test 1: Write operation
    address = 32'h0000_0001;
    pr_write_data_in = 32'b1010101010;
    write_in = 1;
    #10;
    //write_in = 0;

    // Wait for write to complete
    //wait (write_ack == 1);
    //#10;

    // Test 2: Read operation
    address = 32'h0000_0001;
    read_in = 1;
    #10;
    //read_in = 0;

    // Wait for read to complete
    //wait (read_ack == 1);
    //#10;

    // Additional tests can be added here

    // End of simulation
    $stop;
  end
endmodule
