
interface slave_intf(input bit PCLK,PRESETn);
    logic PSELx;
    logic PENABLE;
    logic PWRITE;
    logic PADDR;
    logic PWDATA;
    logic PRDATA;
    logic PREADY;
    logic PSLVERR;

  clocking sdrv_cb@(posedge PCLK);
	default input #1step output #1ns;
    output PSELx;
    output PENABLE;
    output PWRITE;
    output PADDR;
    output PWDATA;
    input PRDATA;
    input PREADY;
    input PSLVERR;
  endclocking  
  
  clocking smon_cb@(posedge PCLK);
	default input #1step;	
    input PSELx;
    input PENABLE;
    input PWRITE;
    input PADDR;
    input PWDATA;
    input PRDATA;
    input PREADY;
    input PSLVERR;
  endclocking
 
   
    modport sdrv_mp(clocking sdrv_cb,input PCLK,PRESETn);
    modport smon_mp(clocking smon_cb,input PCLK,PRESETn);  
  
    
endinterface

