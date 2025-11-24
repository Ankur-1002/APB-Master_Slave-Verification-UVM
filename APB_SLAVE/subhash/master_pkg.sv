package master_pkg;
  `define ADDR_WIDTH 32
  `define DATA_WIDTH 32
  `define MEM_DEPTH 256


  `include "uvm_macros.svh"
  import uvm_pkg::*;
  `include "master_tx.sv"
  `include "master_seq_lib.sv"
  `include "master_mon.sv"
  `include "master_drv.sv"
  `include "master_sqr.sv"
  `include "master_agnt.sv"
  `include "master_env.sv"
  `include "master_test_lib.sv"

endpackage
