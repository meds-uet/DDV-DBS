module 7segment_decoder_tb;
    reg [3:0] in;
    wire [6:0] out;
    
    e1t2 uut (
         .in(in), 
         .out(out)
    );
    reg [6:0] out2;

    initial begin
        for (in = 0; in < 16; in = in + 1) begin
            #10;
            case (in)
                4'b0000: out2 = 7'b1111110; // 0
                4'b0001: out2 = 7'b0110000; // 1
                4'b0010: out2 = 7'b1101101; // 2
                4'b0011: out2 = 7'b1111001; // 3
                4'b0100: out2 = 7'b0110011; // 4
                4'b0101: out2 = 7'b1011011; // 5
                4'b0110: out2 = 7'b1011111; // 6
                4'b0111: out2 = 7'b1110000; // 7
                4'b1000: out2 = 7'b1111111; // 8
                4'b1001: out2 = 7'b1111011; // 9
                4'b1010: out2 = 7'b1110111; // A
                4'b1011: out2 = 7'b0011111; // b
                4'b1100: out2 = 7'b1001110; // C
                4'b1101: out2 = 7'b0111101; // d
                4'b1110: out2 = 7'b1001111; // E
                4'b1111: out2 = 7'b1000111; // F
                default: out2 = 7'b0000000; // default off
            endcase
            
            if (out !== out2) begin
                $display("ERROR: in = %b, out = %b, Expected = %b", in, out, out2);
            end else begin
                $display("in = %b, out = %b, Expected = %b", in, out, out2);
            end
        end
        
        $finish; 
    end
endmodule
