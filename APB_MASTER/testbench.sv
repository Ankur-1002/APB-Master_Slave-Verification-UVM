// Code your testbench here
// or browse Examples
`include "uvm_macros.svh"
`include "apb_pkg.sv"


import uvm_pkg::*;

import apb_pkg::*;



module apb_tb_top;
    
    logic Pclk;
    
    // Clock generation
    initial begin
        Pclk = 0;
        forever #5 Pclk = ~Pclk;
    end
    
    // Interface instance
    apb_if vif(Pclk);
    
    // DUT instance
    apb_master dut (
        .Pclk(vif.Pclk),
        .Presetn(vif.Presetn),
        .APB_write_paddr(vif.APB_write_paddr),
        .APB_read_paddr(vif.APB_read_paddr),
        .WRITE_READ(vif.WRITE_READ),
        .APB_write_data(vif.APB_write_data),
        .transfer(vif.transfer),
        .Prdata_in(vif.Prdata_in),
        .Pslverr(vif.Pslverr),
        .Pready(vif.Pready),
        .Prdata_out(vif.Prdata_out),
        .slverr_out(vif.slverr_out),
        .Paddr(vif.Paddr),
        .Pwdata(vif.Pwdata),
        .Pwrite(vif.Pwrite),
        .Psel(vif.Psel),
        .Penable(vif.Penable)
    );
    
    // Reset generation
    initial begin
        vif.Presetn = 0;
        repeat(5) @(posedge Pclk);
        vif.Presetn = 1;
    end
    
    // Set interface in config_db
    initial begin
        uvm_config_db#(virtual apb_if)::set(null, "*", "vif", vif);
    end
    
    // Dump waveforms
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, apb_tb_top);
    end
    
    // Run test
    initial begin
      run_test("apb_read_test");
    end
    
    // Timeout
//     initial begin
//         #50000;
//         $display("Timeout!");
//         $finish;
//     end
    
endmodule
