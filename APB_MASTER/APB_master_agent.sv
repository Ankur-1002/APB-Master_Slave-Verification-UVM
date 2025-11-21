class apb_master_agent extends uvm_agent;

	`uvm_component_utils(apb_master_agent)

apb_sequencer m_seqrh;
apb_driver m_drvh;
apb_monitor m_monh;

function new(string name = "apb_master_agent", uvm_component parent);
	super.new(name, parent);
endfunction

function void build_phase(uvm_phase phase);
	super.build_phase(phase);
endfunction

function void connect_phase(uvm_phase phase);
	super.connect_phase(phase);
	m_drvh.seq_item_port.connect(m_seqrh.seq_item_export);
endfunction

endclass

