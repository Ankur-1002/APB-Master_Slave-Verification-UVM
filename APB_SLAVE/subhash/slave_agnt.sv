class slave_agnt extends uvm_agent;

	`uvm_component_utils(slave_agnt)

	slave_sqr s_sqr;
	slave_drv s_drv;
	slave_mon s_mon;

	function new(string name = "slave_agnt", uvm_component parent);
		super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		s_drv = slave_drv::type_id::create("s_drv",this);
		s_mon = slave_mon::type_id::create("s_mon",this);
		s_sqr = slave_sqr::type_id::create("s_sqr",this);		
	endfunction

	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		s_drv.seq_item_port.connect(s_sqr.seq_item_export);
	endfunction


endclass
