class apb_slave_monitor extends uvm_monitor;
	`uvm_component_utils(apb_slave_monitor)

	virtual slave_intf svif;

	uvm_analysis_port#(slave_tx) monitor_port;

	slave_tx txn_1;

	function new(string name = "apb_slave_monitor", uvm_component parent);
		super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
		`uvm_info("slave_monitor","inside build_phase",UVM_LOW)
		monitor_port=new("monitor_port",this);
		txn_1 = slave_tx::type_id::create("txn_1");
		if(!uvm_config_db#(virtual slave_intf)::get(this,"","SVIF",svif))
			`uvm_fatal("SLAVE_MONITOR","cannt get interface")
	endfunction


	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
	endfunction

	task run_phase(uvm_phase phase);
		`uvm_info("SLAVE_MON","MON_RUN_PHASE",UVM_NONE);
		forever	
			collect();
	endtask


	task collect();
		@(svif.smon_cb);
		txn_1.PADDR 	<= svif.smon_cb.PADDR;
		txn_1.PWRITE	<= svif.smon_cb.PWRITE;
		txn_1.PENABLE 	<= svif.smon_cb.PENABLE;
		txn_1.PSELx 	<= svif.smon_cb.PSELx;
		txn_1.PRDATA 	<= svif.smon_cb.PRDATA;
		@(svif.s_mon)
		monitor_port.write(txn_1);
		$display($time," monitor_data=%0d",txn_1.prdata);
	endtask

endclass
