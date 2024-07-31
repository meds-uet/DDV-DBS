module carry_look_ahead_adder_4bit(
    input logic [3:0] A, 
    input logic [3:0] B, 
    output logic [3:0] Sum,
    output logic Cout 
);
    logic [3:0] P; 
    logic [3:0] G; 
    logic [3:0] C; 

    // Propagate and Generate
    assign P = A ^ B;
    assign G = A & B;

    // Carry look-ahead logic
    assign C[0] = G[0];
    assign C[1] = G[1] | (P[1] & G[0]);
    assign C[2] = G[2] | (P[2] & G[1]) | (P[2] & P[1] & G[0]);
    assign C[3] = G[3] | (P[3] & G[2]) | (P[3] & P[2] & G[1]) | (P[3] & P[2] & P[1] & G[0]);
    assign Cout = C[3] | (P[3] & C[2]);

    assign Sum = P ^ {C[2:0], 1'b0};

endmodule
