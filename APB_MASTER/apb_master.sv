`define ADDR_WIDTH 32
`define DATA_WIDTH 32



module apb_master (
                  input logic pclk,presetn,
                  input logic pready,pslverr,
                  input logic[`DATA_WIDTH-1:0]prdata,
                  input logic[`ADDR_WIDTH-1:0]write_addr,read_addr,
                  input logic[`DATA_WIDTH-1:0]write_data,
                  input logic rd_wr,transfer,
                  output logic penable,pwrite,
                  output logic pselx,
                  output logic[`ADDR_WIDTH-1:0]paddr,
                  output logic[`DATA_WIDTH-1:0]pwdata,read_data);
 
  typedef enum logic [1:0]{IDLE=2'b00,SETUP=2'b01,ACCESS=2'b10} state;
  state ps,ns;
 
  always@(posedge pclk or negedge presetn)
    begin
      if(!presetn)
        ps<=IDLE;
      else
        ps<=ns;
    end
  always@(*)begin
     if(!presetn)
       begin
         penable= 0;
         pwdata =0;
         paddr =0;
         pselx=0;
       end
    else
      begin
      case(ps)
      IDLE: begin
              pselx=0;
              penable=0;
              ns=(transfer)? SETUP:IDLE;
             end
 
      SETUP:begin
               pselx=1'b1;
               penable=0;
               pwrite=rd_wr;
              if(rd_wr)
                begin
                  pwdata=write_data;
                  paddr=write_addr;
               end                                  
              else
               begin
                paddr=read_addr; 
               end
 
               ns=ACCESS;
             end
      ACCESS:begin
               penable =1;
               pselx = 1;
               if(pready)
                 begin 
		if(transfer&& !pslverr) begin
			ns=SETUP;
			if(!rd_wr)
		     read_data=prdata;
		end
		else
		begin
		ns=IDLE;
	        end
		end
		else
	 begin
	        ns=ACCESS;
	       end
 
	   end
	default:ns=IDLE;
	endcase
 
  end
end
endmodule


