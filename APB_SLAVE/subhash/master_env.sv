class master_env extends uvm_env;

	`uvm_component_utils(master_env)

	master_agnt m_agnt;

	function new(string name="master_env",uvm_component parent);
		super.new(name,parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		`uvm_info("env","env_build_phase",UVM_LOW);
		m_agnt = master_agnt::type_id::create("m_agnt",this);
	endfunction
	
	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
	endfunction

endclass
