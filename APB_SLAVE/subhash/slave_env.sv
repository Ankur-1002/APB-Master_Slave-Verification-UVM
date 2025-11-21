class slave_env extends uvm_env;

	`uvm_component_utils(slave_env)

	slave_agnt s_agnt;

	function new(string name="slave_env",uvm_component parent);
		super.new(name,parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		`uvm_info("env","env_build_phase",UVM_LOW);
		s_agnt = slave_agnt::type_id::create("s_agnt",this);
	endfunction
	
	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
	endfunction

endclass
