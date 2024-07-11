module tb_sevensegment_display;
logic [6:0] control_input;
logic [3:0] seg;
logic [6:0] verify;
int i;

sevensegment_display uut(
    .control_input(control_input),
    .seg(seg)
);

inital begin
   

    for ( i=0; i< 16; i = i +1) begin
        control_input = i;

        case(control_input) 
        4'b0000: verify = 7'b0111111; //display of 0
        4'b0001: verify = 7'b0000110; //display of 1
        4'b0010: verify = 7'b1011011; // 2
        4'b0011: verify = 7'b1001111; // 3
        4'b0100: verify = 7'b1100110; // 4
        4'b0101: verify = 7'b1101101; // 5
        4'b0110: verify = 7'b1111101; // 6
        4'b0111: verify = 7'b0000111; // 7
        4'b1000: verify = 7'b1111111; // 8
        4'b1001: verify = 7'b1101111; // 9
        4'b1010: verify = 7'b1110111; // A
        4'b1011: verify = 7'b1111100; // b
        4'b1100: verify = 7'b0111001; // C
        4'b1101: verify = 7'b1011110; // d
        4'b1110: verify = 7'b1111001; // E
        4'b1111: verify = 7'b1110001; // F
        endcase
        #10
        $display("At input %b, output is %b, expected is %b", i, seg, verify);
        #10
        if (seg!= verify) begin
            $display("Mismatch detected");
        end
    end
    $finish;
end
endmodule








end