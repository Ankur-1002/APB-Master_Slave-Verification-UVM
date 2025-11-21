class apb_slave_agent extends uvm_agent;

	`uvm_component_utils(apb_slave_agent)

apb_slave_sequencer s_seqrh;
apb_slave_driver s_drvh;
apb_slave_monitor s_monh;

function new(string name = "apb_slave_agent", uvm_component parent);
	super.new(name, parent);
endfunction

function void build_phase(uvm_phase phase);
	super.build_phase(phase);
endfunction

function void connect_phase(uvm_phase phase);
	super.connect_phase(phase);
	s_drvh.seq_item_port.connect(s_seqrh.seq_item_export);
endfunction

endclass
