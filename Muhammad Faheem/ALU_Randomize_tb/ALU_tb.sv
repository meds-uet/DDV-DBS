module ALU_tb;

    // Testbench signals
    logic [15:0] A, B;
    logic [2:0] C;
    logic [15:0] Y;

    // Instantiate the ALU
    ALU_16bit uut (
        .A(A),
        .B(B),
        .C(C),
        .Y(Y)
    );
    
initial begin
      #10;
      ALU_in();
  	  Alu_checker();
      #10
      ALU_in();
  	  Alu_checker();
      #10
      ALU_in();
  	  Alu_checker();
end
  
  task Alu_checker;
    begin
      // Check expected results using assertions
      case (C)
        3'd0: assert(Y == A + B) else $display("Addition failed: A=%h, B=%h, Y=%h, t=%t", A, B, Y,$time);
        3'd1: assert(Y == A - B) else $display("Subtraction failed: A=%h, B=%h, Y=%h, t=%t", A, B, Y,$time);
        3'd2: assert(Y == A & B) else $display("AND operation failed: A=%h, B=%h, Y=%h, t=%t", A, B, Y,$time);
        3'd3: assert(Y == A | B) else $display("OR operation failed: A=%h, B=%h, Y=%h, t=%t", A, B, Y,$time);
        3'd4: assert(Y == A ^ B) else $display("XOR operation failed: A=%h, B=%h, Y=%h, t=%t", A, B, Y,$time);
      endcase
    end
  endtask
    
task ALU_in;
begin
    // Generate random inputs
        A = $urandom();
        B = $urandom();
        C = $urandom() % 5; // Generate random operation code from 0 to 4
    end
    endtask
  
 initial begin
    // Open dump file for waveform analysis
    $dumpfile("ALU_tb.vcd");
   $dumpvars(0, ALU_tb);
 end
  
 initial begin
 #100
 $finish;
 end   
endmodule