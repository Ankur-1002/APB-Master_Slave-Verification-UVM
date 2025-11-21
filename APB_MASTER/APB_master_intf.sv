
interface apb_if(input bit Pclk,Presetn);
  //logic Pclk;
  //logic Prst;
  logic Pwrite;
  logic Pread;
  logic Pready;
  logic [ADDR_WIDTH-1:0] Pwdata;
  logic Psel;
  logic Pslverr;
  logic [ADDR_WIDTH-1:0] Prdata;
  logic Penable;
  logic Paddr;
  logic transfer;
 
  clocking mdrv_cb@(posedge Pclk);
	default input #1step output #1ns;
    output Pwrite;
    output Pread;
    output Pwdata;
    output Psel;
    output Pslverr;
    output Penable;
    output Paddr;
    output transfer; 	// 
    input  Prdata;
    input  Pready;    
  endclocking
  
  clocking mmon_cb@(posedge Pclk);
	default input #1step;
    input Pwrite;
    input Pread;
    input Pwdata;
    input Prdata;
    input Psel;
    input Penable;
    input Pslverr;
    input Paddr;
    input Pready;
    input transfer;		//
  endclocking
 
  
 
  
  
  
  
    modport mdrv_mp(clocking mdrv_cb,input Pclk,Presetn);
    modport mmon_mp(clocking mmon_cb,input Pclk,Presetn);
    
    
   
   
  

    
endinterface

