  `define ADDR_WIDTH 32 
  `define DATA_WIDTH 32
  `define MEM_DEPTH 1024
  `include "uvm_pkg.sv"
   import uvm_pkg::*; 
  `include "uvm_macros.svh"
   `include "master_intf.sv"
   `include "apb_slave.sv"

  `include "master_tx.sv"
  `include "master_sbd.sv"
  `include "master_cov.sv"
  `include "master_mon.sv"
  `include "master_drv.sv"
  `include "master_sqr.sv"
  `include "master_agnt.sv"
  `include "master_env.sv"
  `include "master_seq_lib.sv"
  `include "master_test_lib.sv"


module top;
	bit PCLK;
	bit PRESETn;

	int num_tx;

	master_intf m_pif(PCLK,PRESETn);

	//CLK generation
	always #5 PCLK = ~PCLK;

	//DUT instantation
	apb_slave s_DUT(
    .PCLK   (m_pif.PCLK),
    .PRESETn(m_pif.PRESETn),
    .PADDR  (m_pif.PADDR),
    .PENABLE(m_pif.PENABLE),
    .PSELx  (m_pif.PSELx),
    .PWRITE (m_pif.PWRITE),
    .PWDATA (m_pif.PWDATA),
    .PRDATA (m_pif.PRDATA),
    .PREADY (m_pif.PREADY),
    .PSLVERR(m_pif.PSLVERR)
   );

	initial begin
      run_test("first_test");
	end

	initial begin
		uvm_config_db#(virtual master_intf)::set(null,"*","MVIF",m_pif);
		PRESETn = 0;
		repeat(2)
			@(posedge PCLK) PRESETn = 1;
	end
	
	//initial begin
   	//	$dumpfile("dump.vcd");
    //	$dumpvars(0, top);
	//end

	initial begin
    	assert($value$plusargs("num_tx=%0d", num_tx));
    	uvm_config_db#(int)::set(null,"*","NUM_TX", num_tx);
	end

endmodule

