
class transaction;
    rand bit X;
	bit det;
   
    constraint  bit_seq{  
    X dist {1 :/ 50 , 0 :/ 50};  
    }
  
    function void display();
      $display("X : %0b \t det: %0b", X,det);
    endfunction
  
    function transaction copy();
        copy = new();
        copy.X = this.X;
        copy.det = this.det;
    endfunction
  
endclass