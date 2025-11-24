`include "master_pkg.sv"
`include "master_intf.sv"
import master_pkg::*;

module top;
	bit PCLK;
	bit PRESETn;

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
	
initial begin
    $dumpfile("dump.vcd");
    $dumpvars(0, top);
end


endmodule
