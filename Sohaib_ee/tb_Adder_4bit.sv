
module tb_Adder_4bit();

// Input 
logic [3:0] a,b;
logic  cin;

//output 
 logic [3:0] sum;
 logic cout;
 
 // instantiation
 
Adder_4bit DUT(.a(a),.b(b),.cin(cin),.sum(sum),.cout(cout));


 // test vectors 
 initial begin
 cin=0;
 for(int i=0;i<16;i++) begin 
   
    for(int j=0;j<16;j++) begin 
	a=i;
	b=j;
	#10;
 $display(" a=%b,b=%b,sum=%b, cout=%b", a, b, sum, cout);
 end
  
 end
  $stop;
 en d 
 
 
 endmodule
 
 
 
 
 
 
 