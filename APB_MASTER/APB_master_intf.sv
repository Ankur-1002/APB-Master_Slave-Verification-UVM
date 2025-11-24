`include "define.sv"
interface apb_if(input logic Pclk);
    
    logic Presetn;
    logic [`ADDR_WIDTH-1:0] APB_write_paddr;
    logic [`ADDR_WIDTH-1:0] APB_read_paddr;
    logic WRITE_READ;
    logic [`DATA_WIDTH-1:0] APB_write_data;
    logic transfer;
    logic [`DATA_WIDTH-1:0] Prdata_in;
    logic Pslverr;
    logic Pready;
    logic [`DATA_WIDTH-1:0] Prdata_out;
    logic slverr_out;
    logic [`ADDR_WIDTH-1:0] Paddr;
    logic [`DATA_WIDTH-1:0] Pwdata;
    logic Pwrite;
    logic Psel;
    logic Penable;
    
    // Clocking blocks for driver and monitor
    clocking driver_cb @(posedge Pclk);
        output APB_write_paddr;
        output APB_read_paddr;
        output WRITE_READ;
        output APB_write_data;
        output transfer;
        output Prdata_in;
        output Pslverr;
        output Pready;
        input Prdata_out;
        input slverr_out;
        input Paddr;
        input Pwdata;
        input Pwrite;
        input Psel;
        input Penable;
    endclocking
    
    clocking monitor_cb @(posedge Pclk);
        input APB_write_paddr;
        input APB_read_paddr;
        input WRITE_READ;
        input APB_write_data;
        input transfer;
        input Prdata_in;
        input Pslverr;
        input Pready;
        input Prdata_out;
        input slverr_out;
        input Paddr;
        input Pwdata;
        input Pwrite;
        input Psel;
        input Penable;
    endclocking
    
    modport DRIVER (clocking driver_cb, input Pclk, output Presetn);
    modport MONITOR (clocking monitor_cb, input Pclk, Presetn);
    
endinterface
