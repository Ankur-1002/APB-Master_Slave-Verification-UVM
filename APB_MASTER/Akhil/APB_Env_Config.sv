class env_config extends uvm_object;

	`uvm_object_utils(env_config)
	apb_master_config m_cnfg;
	apb_slave_config s_cnfg;
		
	virtual apb_if vif;
	uvm_active_passive_enum is_active = UVM_ACTIVE;
	bit has_scoreboard = 1;
	bit has_m_agnth = 1;
	bit has_s_agnth = 1;

function new(string name = "env_config");
	super.new(name);
endfunction

endclass
