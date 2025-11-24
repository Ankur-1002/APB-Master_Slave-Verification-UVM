module top;
	bit PCLK;
	bit PRESETn;

	slave_intf s_pif(PCLK,PRESETn);

	//CLK generation
	always #5 PCLK = ~PCLK;

	//DUT instantation
	apb_slave s_DUT(
    .PCLK   (s_pif.PCLK),
    .PRESETn(s_pif.PRESETn),
    .PADDR  (s_pif.PADDR),
    .PENABLE(s_pif.PENABLE),
    .PSELx  (s_pif.PSELx),
    .PWRITE (s_pif.PWRITE),
    .PWDATA (s_pif.PWDATA),
    .PRDATA (s_pif.PRDATA),
    .PREADY (s_pif.PREADY),
    .PSLVERR(s_pif.PSLVERR)
   );

	initial begin
		run_test("");
	end
	initial begin
		uvm_config_db#(virtual mem_intf)::set(null,"*","SVIF",s_pif);
		PRESETn = 0;
		repeat(2)
			@(posedge PCLK) PRESETn = 1;
	end


endmodule
