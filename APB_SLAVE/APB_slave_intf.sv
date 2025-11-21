
interface slave_intf(input bit Pclk,Presetn);
  //logic Pclk;
  //logic Prst;
  logic PWRITE;
  logic PREADY;
  logic [`ADDR_WIDTH-1:0] PWDATA;
  logic PSELx;
  logic PSLVERR;
  logic [`ADDR_WIDTH-1:0] PRDATA;
  logic PENABLE;
  logic PADDR;
 
 
 
  
  clocking sdrv_cb@(posedge Pclk);
	default input #1step output #1ns;
    input PWRITE;
    input  PWDATA;
    input  PSELx;
    input  PSLVERR;
    input  Penable;
   input  PADDR; 
   output  PRDATA;
   output PREADY;
    
  endclocking  
  
  clocking smon_cb@(posedge Pclk);
	default input #1step;	
    input PWRITE;
    input PWDATA;
    input PRDATA;
    input PSELx;
    input Penable;
    input PSLVERR;
    input PADDR;
    input PREADY;
    
  endclocking
 
 
  
    
   
    modport sdrv_mp(clocking sdrv_cb,input Pclk,Presetn);
    modport smon_mp(clocking smon_cb,input Pclk,Presetn);  
  

    
endinterface

