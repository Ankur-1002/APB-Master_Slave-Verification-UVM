class apb_slave_driver extends uvm_driver;
		`uvm_component_utils(apb_slave_driver)

		virtual slave_intf svif;

		function new(string name = "apb_slave_driver", uvm_component parent);
			super.new(name, parent);
		endfunction

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			`uvm_info("slave_driver","inside build_phase",UVM_LOW)
			if(!uvm_config_db#(virtual slave_intf)::get(this,"","SVIF",svif))
				`uvm_fatal("SLAVE_DRIVER","cannt get interface")
		endfunction

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
		endfunction

		task run_phase(uvm_phase phase);
			wait(vif.PRESETn == 1);
			forever begin
				seq_item_port.get_next_item(req);
				drive_tx(req);
				seq_item_port.item_done();
			end

		endtask

		task drive_tx(slave_tx txn);
			@(svif.drv_cb);
			svif.sdrv_cb.PADDR    	<= txn.PADDR;
			svif.sdrv_cb.PSELx    	<= txn.PSELx;
			svif.sdrv_cb.PENABLE  	<= txn.PENABLE;
			svif.sdrv_cb.PWRITE   	<= txn.PWRITE;
			if(txn.PWRITE == 1) 
				svif.sdrv_cb.PWDATA 	<= txn.PWDATA;
			//wait(txn.PREADY);
			//svif.sdrv_cb.PADDR    	<= '0; 
			//svif.sdrv_cb.PSELx    	<= '0;
			//svif.sdrv_cb.PENABLE  	<= '0;
			//svif.sdrv_cb.PWRITE   	<= '0;
			//svif.sdrv_cb.PWDATA 		<= '0;
		endtask


endclass
