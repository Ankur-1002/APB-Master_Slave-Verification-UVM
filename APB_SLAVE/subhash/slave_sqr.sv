class slave_sqr extends uvm_sequencer#(slave_tx);
	`uvm_component_utils(apb_slave_sequencer)

	function new(string name = "slave_sqr", uvm_component parent);
		super.new(name, parent);
	endfunction

endclass
