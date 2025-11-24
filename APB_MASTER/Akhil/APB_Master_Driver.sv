class apb_driver extends uvm_driver #(apb_transaction);
	
	`uvm_component_utils(apb_driver)

	apb_transaction req;
	virtual apb_if m_vif;

		function new(string name = "apb_driver", uvm_component parent);
			super.new(name, parent);
		endfunction

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			req = apb_transaction :: type_id :: create("req");
		endfunction

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
		endfunction

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
				forever
					begin
						seq_item_port.get_next_item(req);
						drive_item(req);
						deq_item_port.item_done();
					end
		endtask

		task drive_item(apb_transaction item);
			@(m_vif.mdrv_cb);
			m_vif.mdrv_cb.Paddr <= item.Paddr;
			m_vif.mdrv_cb.Pwrite <= item.Pwrite;
			m_vif.mdrv_cb.Pwdara <= item.Pwdata;
			m_vif.mdrv_cb.Pwrite <= item.Pwrite;
			m_vif.mdrv_cb.Psel <= 1;
			m_vif.mdrv_cb.Penable <= 0;
		//    	m_vif.mdrv_cb.transfer <= 1;

			@(m_vif.mdrv_cb);
			m_vif.mdrv_cb.Penable <= 1;

			do
				begin
					@(m_vif.mdrv_cb)
				end
			while
				(!m_vif.mdrv_cb.Pready);

			@(m_vif.mdrv_cb)// Without Transfer
				m_vif.mdrv_cb.Penable <= 0;
		/*With Transfer Signal		
			if(m_vif.mdrv_cb.Pready && m_vif.mdrv_cb.transfer)
				begin
					m_vif.mdrv_cb.Psel <= 1;
					m_vif.mdrv_cb.Penable <= 0;
				end
			else
				begin
					m_vif.mdrv_cb.Psel <= 0;
					m_vif.mdrv_cb.Penable <= 0;
				end*/
		endtask

endclass
