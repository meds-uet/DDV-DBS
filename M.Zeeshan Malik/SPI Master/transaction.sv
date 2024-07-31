class transaction;
  
  rand logic [7:0] tx_data;
  logic [7:0] rx_data;
  rand logic start_transaction;
  rand logic miso;
  
  function void display(string name);
    $display("---------------------------");
    $display("%s", name);
    $display("---------------------------");
    $display("tx_data = %0d, rx_data = %0d", tx_data, rx_data);
    $display("start_transaction = %0d", start_transaction);
    $display("miso = %0d", miso);
    $display("---------------------------");
  endfunction
  
// Constraint block to randomize start_transaction
  constraint c_start_transaction {
    start_transaction == 1'b1; // Constraint to set start_transaction to 1
  }
  // Constraint block to randomize miso
  constraint c_miso {
    miso == 1'b1; // Constraint to set miso to either 0 or 1
  }


endclass