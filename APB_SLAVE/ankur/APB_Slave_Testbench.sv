`include "uvm_macros.svh"    // UVM macros
`include "APB_Pkg.sv"        // APB package

import uvm_pkg::*;           //to import all the uvm packages
import apb_pkg::*;

module tb;

  //clock generation and reset
  bit PCLK;
  bit PRESETn;

  //interface instantiation 
  intf inf(PCLK); //check the names coz i dunno

  //--------------------------------------------------------------------
  //Clock generation
  //--------------------------------------------------------------------
  initial begin 
    PCLK = 0 ;
    forever begin 
        #5 PCLK = ~PCLK;    //generates 100 MHZ clock or 10ns
    end
  end

  //--------------------------------------------------------------------
  //PRESETn generation
  //--------------------------------------------------------------------

  initial begin 
    PRESETn = 1'b0;
    #20;
    PRESETn = 1'b1;    //to release the reset after 20ns
  end

  //--------------------------------------------------------------------
  //DUT INSTANTIATION
  //--------------------------------------------------------------------
 apb_slave dut (
    .PCLK    (inf.PCLK),
    .PRESETn (inf.PRESETn),
    .PSEL    (inf.PSEL),
    .PENABLE (inf.PENABLE),
    .PWRITE  (inf.PWRITE),
    .PADDR   (inf.PADDR),
    .PWDATA  (inf.PWDATA),
    .PRDATA  (inf.PRDATA),
    .PSLVERR (inf.PSLVERR),
    .PREADY  (inf.PREADY)
  );
  //--------------------------------------------------------------------
  //UVM Configuration setup
  //--------------------------------------------------------------------
initial begin 
  uvm_config_db #(virtual intf)::set(null,"*","inf",inf);
end
  //--------------------------------------------------------------------
  //Waveform dump
  //--------------------------------------------------------------------
  initial begin 
    $dumpfile("dump.vcd");
    $dumpvars(0,tb);
  end
//test case run
  initial begin 
    run_test("test_name");
  end
endmodule

