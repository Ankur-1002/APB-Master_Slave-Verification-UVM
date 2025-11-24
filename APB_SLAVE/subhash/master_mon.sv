class master_mon extends uvm_monitor;
	`uvm_component_utils(master_mon)

	virtual master_intf mvif;

	uvm_analysis_port#(master_tx) monitor_port;

	master_tx txn_1;

	function new(string name = "master_mon", uvm_component parent);
		super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
		`uvm_info("master_mon","inside build_phase",UVM_LOW)
		monitor_port=new("monitor_port",this);
		txn_1 = master_tx::type_id::create("txn_1");
		if(!uvm_config_db#(virtual master_intf)::get(this,"","MVIF",mvif))
			`uvm_fatal("MASTER_MONITOR","cannt get interface")
	endfunction


	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
	endfunction

	task run_phase(uvm_phase phase);
		`uvm_info("MASTER_MON","MON_RUN_PHASE",UVM_NONE);
		forever	
			collect();
	endtask


	task collect();
		@(mvif.mmon_cb);
		txn_1.PADDR 	<= mvif.mmon_cb.PADDR;
		txn_1.PWRITE	<= mvif.mmon_cb.PWRITE;
		txn_1.PENABLE 	<= mvif.mmon_cb.PENABLE;
		txn_1.PSELx 	<= mvif.mmon_cb.PSELx;
		txn_1.PRDATA 	<= mvif.mmon_cb.PRDATA;
		@(mvif.mmon_cb);
		//monitor_port.write(txn_1);
      //$display($time," monitor_data=%0d",txn_1.PRDATA);
//       txn_1.print();
	endtask

endclass
