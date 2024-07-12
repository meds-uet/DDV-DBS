module AXI4_Lite_Slave_Address(

       // General Inputs

         input logic clk,
         input logic reset,

      // Write Address Channel
         input logic [31:0] awaddr,
         input logic [2:0] awprot,
         input logic awvalid,
         output logic awready,
 
      // Write Data Channel
         input logic [31:0] wdata,
         input logic [3:0] wstrb,
         input logic wvalid,
         output logic wready,

      // Write Response Channel
         output logic [1:0] bresp,
         output logic bvalid,
         input logic bready,
   
      // Read Address Channel
         input logic [31:0] araddr,
         input logic [2:0] arprot,
         input logic arvalid,
         output logic arready,

      // Read Data Channel
    	 output logic [31:0] rdata,
   	 output logic [1:0] rresp,
    	 output logic rvalid,
    	 input  logic rready
);

     logic [31:0] reg_file [0:15];
     
     
     logic [31:0] write_addr;
     logic [31:0] read_addr;

    typedef enum logic [1:0] {IDLE_W, Write_Address, Write_DataChannel, Response} write_state_t;
    write_state_t write_state;
   
    typedef enum logic [1:0] {IDLE_R, Read_Address, Read_Data,  Data_Return} read_state_t;
    read_state_t read_state;
        
     always_ff @(posedge clk or posedge reset)begin
         if(reset)begin
             write_state <= IDLE_W;
             awready <= 0;
             wready <= 0;
             bvalid <= 0;
             bresp <= 2'b00;
         end else begin
            case( write_state)
               IDLE_W : begin 
                   if ( awvalid)begin
                       awready <= 1;
                       write_addr <= awaddr;
                       write_state <= Write_Address;
                    end
                end
            
               Write_Address : begin
                   awready <= 0;
                   if ( write_addr < 16 && awprot[1:0] == 2'b00) begin
                     wready <= 1;
                     write_state <= Write_DataChannel;
                   end else begin
                     bresp <= 2'b10;
                     write_state <= Response;
                   end
               end
             
               Write_DataChannel: begin
                   if ( wvalid && wready)begin
                     for (int i = 0; i < 4; i++) begin
            	       if (wstrb[i]) begin
                	   reg_file[write_addr[3:0]][8*i +: 8] <= wdata[8*i +: 8];
            	       end
       		     end
                   wready <= 0;
       		   bvalid <= 1;
       		   bresp <= 2'b00; // OKAY response
      		   write_state <= Response;
  		 end
	       end

               Response : begin
                   if ( bvalid && bready ) begin
                      bvalid <= 0;
                      write_state <= IDLE_W;
                   end
               end
        endcase
     end
 end

always_ff @ (posedge clk or posedge reset) begin
      if( reset)begin
         arready <= 0;
         rresp <= 2'b00;
         rvalid <= 0;
         read_state <= IDLE_R;
      end else begin
	 case (read_state)
                IDLE_R: begin
                    if (arvalid) begin
                        arready <= 1;
                        read_addr <= araddr;
                        read_state <= Read_Address;
                    end
                end

                Read_Address: begin
                    arready <= 0; 
                    if (read_addr < 16 && arprot[1:0] == 2'b00) begin
                        read_state <= Read_Data;
                    end else begin
                        rresp <= 2'b10;
                        read_state <= Data_Return;
                    end
                end

                Read_Data: begin
                    rdata <= reg_file[read_addr];
                    rvalid <= 1;
                    rresp <= 2'b00; // OKAY response
                    read_state <= Data_Return;
                end

                Data_Return: begin
                    if (rready && rvalid) begin
                        rvalid <= 0;
                        read_state <= IDLE_R;
                    end
                end
            endcase
        end
    end
endmodule
         
                            
             
                         

     
 
     

