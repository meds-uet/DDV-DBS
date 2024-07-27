class spi_scoreboard;
  mailbox #(logic [7:0]) expected_data_mbox;
  mailbox #(logic [7:0]) actual_data_mbox;

  function new(mailbox #(logic [7:0]) expected_data_mbox, mailbox #(logic [7:0]) actual_data_mbox);
    this.expected_data_mbox = expected_data_mbox;
    this.actual_data_mbox = actual_data_mbox;
  endfunction

  task compare();
    logic [7:0] expected_data;
    logic [7:0] actual_data;
    forever begin
      expected_data_mbox.get(expected_data);
      actual_data_mbox.get(actual_data);
      if (expected_data !== actual_data) begin
        $display("Mismatch: expected %h, got %h", expected_data, actual_data);
      end
    end
  endtask
endclass
