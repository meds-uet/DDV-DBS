module Count#(parameter w=4) 
(   input logic[w-1:0] a, // a is the initial value of input 
    input logic sel, reset, clk,  // sel is for up and down count
    output logic [w-1:0] b);

    always_ff @(posedge clk ) begin
        if (reset) begin
            b <= a;    
        end  
        
        else if (sel) begin
            b++;
        end
         
        else begin 
            b--;
        end    
    end
endmodule
