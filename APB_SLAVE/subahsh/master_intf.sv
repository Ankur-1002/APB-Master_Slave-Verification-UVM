// `define ADDR_WIDTH 32
// `define DATA_WIDTH 32
// `define MEM_DEPTH 256 

interface master_intf(input bit PCLK,PRESETn);
    logic PSELx;
    logic PENABLE;
    logic PWRITE;
  	logic [`ADDR_WIDTH-1:0] PADDR;
  	logic [`DATA_WIDTH-1:0] PWDATA;
  	logic [`DATA_WIDTH-1:0] PRDATA;
    logic PREADY;
    logic PSLVERR;

  clocking mdrv_cb@(posedge PCLK);
	default input #1 output #0;
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
	default input #0;	
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


