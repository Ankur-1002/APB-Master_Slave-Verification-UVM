class apb_driver extends uvm_driver #(apb_transaction);
    
    `uvm_component_utils(apb_driver)
    apb_master_config m_cfg;
    virtual apb_if vif;
    
    function new(string name = "apb_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(apb_master_config)::get(this, "", "apb_master_config", m_cfg))
            `uvm_fatal(get_type_name(), "Virtual interface not found!")
    endfunction

	function void connect_phase(uvm_phase phase);
		vif = m_cfg.vif;
	endfunction

    
    task run_phase(uvm_phase phase);
			super.run_phase(phase);
				forever
					begin
						seq_item_port.get_next_item(req);
						`uvm_info(get_full_name(),"Wait for the sequence item", UVM_MEDIUM)
						drive_item(req);
						seq_item_port.item_done();
					end
		endtask

		task drive_item(apb_transaction req);
			@(vif.mdrv_cb);
			vif.mdrv_cb.PADDR <= req.paddr;
			vif.mdrv_cb.PWRITE <= req.pwrite;
			vif.mdrv_cb.PWDATA <= req.pwdata;
			vif.mdrv_cb.PWRITE <= req.pwrite;
			vif.mdrv_cb.PSELx <= req.pselx;
			vif.mdrv_cb.PENABLE <= 0;

			@(vif.mdrv_cb);
			vif.mdrv_cb.PENABLE <= 1;

		/*	do
				begin
					@(vif.mdrv_cb);
				end
			while
				(!vif.mdrv_cb.PREADY);*/
			wait(!vif.mdrv_cb.PREADY);

			@(vif.mdrv_cb)// Without Transfer
				vif.mdrv_cb.PENABLE <= 0;
			endtask

endclass
