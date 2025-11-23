//==========================================================================
`include "APB_Define.sv"
`include "APB_Slave_Intf.sv"
package apb_pkg;
 `include "uvm_macros.svh"
  import uvm_pkg::*;
 `include "APB_Slave_Txn.sv"
 `include "APB_Slave_Sequence.sv"
 `include "APB_Slave_Sequencer.sv"
 `include "APB_Slave_Driver.sv"
 `include "APB_Slave_Monitor.sv"
 `include "APB_Slave_Agent.sv"
 //`include "APB_reference_model.sv"
 //`include "APB_Slave_Scoreboard.sv"
 `include "APB_Slave_Env.sv"
 `include "APB_Slave_Test.sv"

endpackage: apb_pkg

