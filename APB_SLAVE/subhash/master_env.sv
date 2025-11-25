class master_env extends uvm_env;

	`uvm_component_utils(master_env)

	master_agnt m_agnt;
   	master_sbd m_sbd;
    master_cov m_cov;

	function new(string name="master_env",uvm_component parent);
		super.new(name,parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		`uvm_info("env","env_build_phase",UVM_LOW);
		m_agnt = master_agnt::type_id::create("m_agnt",this);
       	m_sbd = master_sbd::type_id::create("m_sbd",this);
        m_cov  = master_cov::type_id::create("m_cov" , this);
	endfunction
	
	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
       	m_agnt.m_mon.monitor_port.connect(m_sbd.sb_imp);
        m_agnt.m_mon.monitor_port.connect(m_cov.ap_imp);
	endfunction

endclass

