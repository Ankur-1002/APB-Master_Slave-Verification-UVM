`default_nettype none


module apb_top #(
parameter ADDR_WIDTH = 8,
	  DATA_WIDTH = 16,
	  DEPTH = 2**ADDR_WIDTH)
(
    // Clock and Reset
  input logic pclk,presetn,
                  input logic pready,pslverr,
                  input logic[DATA_WIDTH-1:0]prdata,
                  input logic[ADDR_WIDTH-1:0]write_addr,read_addr,
                  input logic[DATA_WIDTH-1:0]write_data,
                  input logic rd_wr,transfer,
    
   output logic[DATA_WIDTH-1:0]read_data);


   logic 
 

  
   
 endmodule
 
