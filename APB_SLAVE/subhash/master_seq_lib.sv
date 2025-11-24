class master_seq_lib extends uvm_sequence#(master_tx);
	`uvm_object_utils(master_seq_lib)
	
	function new(string name="master_seq_lib");
		super.new(name);
	endfunction

	task pre_body;
		'uvm_info("master_seq_lib","pre_body",UVM_NONE);
	endtask

	task post_body();
		'uvm_info("master_seq_lib","post_body",UVM_NONE);
	endtask

endclass

class RESET_SEQ extends master_seq_lib;
	`uvm_object_utils(RESET_SEQ)

	master_tx tx;

	function new(string name="");
		super.new(name);
	endfunction

	task body();
		`uvm_do_with(req,{req.PRESETn==0;})
	endtask

endclass

class WR_RD_SEQ extends master_seq_lib;
	`uvm_object_utils(WR_RD_SEQ)

	master_tx tx;

	function new(string name="");
		super.new(name);
	endfunction

	task body();
		`uvm_do_with(req,{req.PRESETn==0;})
	endtask


	
endclass
