interface master_intf(input bit PCLK,PRESETn);
    logic PSELx;
    logic PENABLE;
    logic PWRITE;
    logic PADDR;
    logic PWDATA;
    logic PRDATA;
    logic PREADY;
    logic PSLVERR;

  clocking mdrv_cb@(posedge PCLK);
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
  
  clocking mmon_cb@(posedge PCLK);
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
 
   
    modport mdrv_mp(clocking mdrv_cb,input PCLK,PRESETn);
    modport mmon_mp(clocking mmon_cb,input PCLK,PRESETn);  
  
    
endinterface

