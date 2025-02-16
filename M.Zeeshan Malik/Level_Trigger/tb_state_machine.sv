module state_machine_tb;

    parameter N = 8; 

    logic clk;
    logic reset;
    logic X;
    logic output_signal;
    logic [N-1:0] X_history;  
    logic [N-1:0] internal_X_history; 


    state_machine dut (
        .clk(clk),
        .reset(reset),
        .X(X),
        .output_signal(output_signal)
    );

    
    shift_register #(
        .N(N)
    ) x_shift_register (
        .clk(clk),
        .reset(reset),
        .shift_left(1'b1), 
        .data_in(X),  
        .data_out(internal_X_history)
    );

   
    logic X_queue[$];

    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    task apply_inputs(logic r, logic x, int cycles);
        reset = r;
        X = x;
        repeat (cycles) @(posedge clk);
    endtask

   
    task check_output(logic expected_output);
        if (output_signal !== expected_output) begin
            $display("Error at time %0t: output_signal = %b, expected = %b", $time, output_signal, expected_output);
        end else begin
            $display("Output is correct at time %0t: output_signal = %b", $time, output_signal);
        end
    endtask

  
    task monitor_signals();
        logic prev_X;
        prev_X = X;

        forever begin
            @(posedge clk);


            if (X_queue.size() == N)
                X_queue.pop_front();
            X_queue.push_back(prev_X);


	   for (int i = 0; i < X_queue.size(); i++) begin
                X_history[i] <= X_queue[i];
            end


           for (int i = 0; i < X_queue.size(); i++) begin
            $display("X_queue[%0d] = %0d", i, X_queue[i]);
           end


            if (prev_X == 0 && X == 1) begin
                $display("Detected rising edge of X at time %0t", $time);
                @(posedge clk); check_output(1);
                @(posedge clk); check_output(0);
            end

           prev_X = X;
        end
    endtask




    initial begin
        reset = 1;
        X = 0;

       
        fork
            monitor_signals();
        join_none

        
        apply_inputs(1, 0, 1);
        apply_inputs(0, 0, 1);
        apply_inputs(0, 0, 1);
        apply_inputs(0, 1, 1);
        apply_inputs(0, 1, 1);
        apply_inputs(0, 1, 1);
        apply_inputs(0, 1, 1);
        apply_inputs(0, 0, 1);
        apply_inputs(0, 1, 1);
        apply_inputs(0, 1, 1);
        apply_inputs(0, 0, 1);

        
        $finish ;
     end
endmodule
