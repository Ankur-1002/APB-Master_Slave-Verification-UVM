class master_drv extends uvm_driver;
		`uvm_component_utils(master_drv)

		virtual master_intf mvif;

		function new(string name = "master_drv", uvm_component parent);
			super.new(name, parent);
		endfunction

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			`uvm_info("master_driver","inside build_phase",UVM_LOW)
			if(!uvm_config_db#(virtual master_intf)::get(this,"","MVIF",mvif))
				`uvm_fatal("MASTER_DRIVER","cannt get interface")
		endfunction

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
		endfunction

		task run_phase(uvm_phase phase);
			wait(mvif.PRESETn == 1);
			forever begin
				seq_item_port.get_next_item(req);
				drive_tx(req);
				seq_item_port.item_done();
			end

		endtask

		task drive_tx(master_tx txn);
			@(mvif.drv_cb);
			mvif.mdrv_cb.PADDR    	<= txn.PADDR;
			mvif.mdrv_cb.PSELx    	<= txn.PSELx;
			mvif.mdrv_cb.PENABLE  	<= txn.PENABLE;
			mvif.mdrv_cb.PWRITE   	<= txn.PWRITE;
			if(txn.PWRITE == 1) 
			mvif.mdrv_cb.PWDATA 	<= txn.PWDATA;
			wait(txn.PREADY);
			mvif.mdrv_cb.PADDR    	<= '0; 
			mvif.mdrv_cb.PSELx    	<= '0;
			mvif.mdrv_cb.PENABLE  	<= '0;
			mvif.mdrv_cb.PWRITE   	<= '0;
			mvif.mdrv_cb.PWDATA 	<= '0;
		endtask


endclass
