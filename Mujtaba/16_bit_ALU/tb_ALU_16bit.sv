class random_pkt;
    rand logic [15:0] in1;
    rand logic [15:0] in2;
    rand logic [2:0] control_signal;

    constraint in1_c { in1 >= 16'h0; in1 <= 16'h31; }
    constraint in2_c { in2 >= 16'h0; in2 <= 16'h31; }
    constraint control_signal_c { control_signal >= 3'h0; control_signal <= 3'h5; }
endclass

module tb_ALU_16bit;
    logic [15:0] in1;
    logic [15:0] in2;
    logic [2:0] control_signal;
    logic [15:0] out;

    random_pkt pkt;

    ALU_16bit ALU (
        .in1(in1),
        .in2(in2),
        .control_signal(control_signal),
        .out(out)
    );

    // Correctness Checker
    task scoreboard(input random_pkt packet);
        logic [15:0] expected_out;
        case (packet.control_signal)
            3'b000: expected_out = packet.in1 + packet.in2;
            3'b001: expected_out = packet.in1 - packet.in2;
            3'b010: expected_out = packet.in1 & packet.in2;
            3'b011: expected_out = packet.in1 | packet.in2;
            3'b100: expected_out = packet.in1 ^ packet.in2;
            default: expected_out = 16'hXXXX;
        endcase

        #10; // Wait for ALU to process

        assert (out === expected_out) begin
            case (packet.control_signal)
                3'b000: $display("ALU Output check passed successfully for ADDITION");
                3'b001: $display("ALU Output check passed successfully for SUBTRACTION");
                3'b010: $display("ALU Output check passed successfully for AND");
                3'b011: $display("ALU Output check passed successfully for OR");
                3'b100: $display("ALU Output check passed successfully for XOR");
            endcase
        end else begin
            $fatal("Assertion failed! in1 = 0x%h, in2 = 0x%h, control_signal = 0x%h, expected = 0x%h, actual = 0x%h", packet.in1, packet.in2, packet.control_signal, expected_out, out);
        end
    endtask

    initial begin
        pkt = new();

        for (int i = 0; i < 20; i++) begin
            if (pkt.randomize()) begin
                $display("Randomization of stimulus successful");
                in1 = pkt.in1;
                in2 = pkt.in2;
                control_signal = pkt.control_signal;
            end else begin
                $display("Randomization of stimulus failed!!!");
            end

            #10; // Allow time for inputs to settle

            $display("in1 = 0x%h, in2 = 0x%h, control_signal = 0x%h, output = 0x%h", in1, in2, control_signal, out);
            scoreboard(pkt);
            $display("\n");

            #10;
        end
    end
endmodule
