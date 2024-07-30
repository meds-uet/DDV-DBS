module adder_4bit (
    input logic [3:0] a,
    input logic [3:0] b,
    output logic [4:0] adderout
);
// always remember combinational circuit like adder, decoder, muxer depend on current value only so use assign statement and dont use always@posedge, you can use always @(*)
    assign adderout = a + b; // 5 bit adderout for carry out
 
endmodule
