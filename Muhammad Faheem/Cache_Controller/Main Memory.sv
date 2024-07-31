module memory #(parameter time module_delay = 10ns) (
    input  logic [23:0] address, 
    input  logic [31:0] write_data, 
    input  logic        m_read, 
    input  logic        m_write, 
    output logic [31:0] read_data
);

   typedef logic [31:0] mem_array[0:255];
    mem_array data_mem;

    integer addr;
  
    int seed = 1; // Seed for random number generation

    // Initialize data_mem with random values
    initial begin
        foreach (data_mem[i]) begin
            data_mem[i] = $random(seed);
        end
    end


    always @(m_read) begin
      addr = address[7:0];
        if (m_read) begin
            #module_delay read_data = data_mem[addr];
        end
    end

    always @(m_write) begin
      addr = address[7:0];
        if (m_write) begin
            data_mem[addr] = write_data;
        end
    end

endmodule