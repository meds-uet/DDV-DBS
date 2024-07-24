
Explanation of implemented task:

1. "Full-Adder-4bit" in this task I have implemented the 4 bit full adder with the help of 1-bit full adder. I have instantiate
    1-bit full adder four time in order to add four bits. 4-bit adder have two inputs of four bit a and b and one carry bit c_in.
    Result of addition is stored in the s and carry out bit is stored in c_out.
    
    In testbench I have used the layered testbench approach in using the task. I have created the two task one is for passing value to 
    dut and other other is calculate the expected results.
    
2.  "SevenSegmentDisplay" shows the active and unactive state of seven leds depending upon the input. Input is passed to case statement
    implemented in the combinational block to check the input and unable and disable the leds according to the input. 
    
3.  "Parameterized-counter" is a sequential circuit increcment the counter to from the given value that is input from the user if the 
    counter is "up" and decrement in case of if "down" is set to 1.
    
4.  "ALU-16bit" have the ALU that can perform the different arithmatic and logical operation on the two 16-bit input, operation is perform
    on the basis of "sel" input and result is stored in out.

5.  "Randomized-ALU-Testbench" test the output by generating the random inputs using the $urandom function.

6.  "Shift-Register" I have implemented the Serial In Serial Out(SISO) shift register that shift the value of 4 -bit one by one at the 
     very positive clock edge.

7.  "FSM-Pulse-Detector" detect the input at the every positive edge of the clock if the ouput is 1 at the current positive edge of the 
     clock and 0 at the previous positive clock then output is 1 at the next clock positive edge. If output is 1 it means pulse is detected
     between the two clock edges.
     
     In testbench circuit behavior is tested using the layered testbench and with help of assertions.
    
       







