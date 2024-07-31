
class transaction;
    randc bit [3:0] a, b;
    rand bit cin;
    bit [3:0] s;
    bit cout;
  
    function void display();
        $display("a : %0d \t b: %0d \t cin: %0d \t sum : %0d \t cout: %0d", a, b, cin, s, cout);
    endfunction
  
    function transaction copy();
        copy = new();
        copy.a = this.a;
        copy.b = this.b;
        copy.cin = this.cin;
        copy.cout = this.cout;
        copy.s = this.s;
    endfunction
  
endclass