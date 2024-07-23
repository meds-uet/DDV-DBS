module adder_4b_tb();

    reg unsigned [3:0] a,b;
    wire unsigned [4:0] c;
    integer correct_check = 0; 
    integer incorrect_check = 0; 
    integer total_checks = 0;
     

    adder_4b dut (.a(a),
                  .b(b),
                  .c(c));
    
    integer i,j;
    logic [4:0] c_expected;

    initial begin
        for(i=0; i<16; i++) begin
            for(j=0; j<16; j++) begin
                a = i;
                b = j;
                c_expected = a+b;
                #10;
                if(c==c_expected)begin
                    $display("Check %d-> Passed %d: a = %d b = %d c = %d c_expected = %d", total_checks,correct_check,a,b,c,c_expected);
                    correct_check++;
                end
                else begin
                    $display("Check %d-> Failed %d: a = %d b = %d c = %d c_expected = %d", total_checks,incorrect_check,a,b,c,c_expected);
                    incorrect_check++;
                end 
                total_checks++;
            end
        end
        $display("Total checks = %d Correct = %d Incorrect = %d", total_checks,correct_check,incorrect_check);  
        $finish;     
    end


    initial begin
        $dumpfile("adder_4b.vcd");
        $dumpvars(0,adder_4b_tb);
    end

endmodule
