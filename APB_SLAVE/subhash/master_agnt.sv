class master_agnt extends uvm_agent;

	`uvm_component_utils(master_agnt)

	master_sqr m_sqr;
	master_drv m_drv;
	master_mon m_mon;

	function new(string name = "master_agnt", uvm_component parent);
		super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		m_drv = master_drv::type_id::create("m_drv",this);
		m_mon = master_mon::type_id::create("m_mon",this);
		m_sqr = master_sqr::type_id::create("m_sqr",this);		
	endfunction

	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		m_drv.seq_item_port.connect(m_sqr.seq_item_export);
	endfunction


endclass
