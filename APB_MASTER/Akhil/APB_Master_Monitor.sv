class apb_monitor extends uvm_monitor;

	`uvm_component_utils(apb_monitor)
	
	apb_transaction data_sent;
	virtual apb_if m_vif;

	function new(string name = "apb_monitor", uvm_component parent);
			super.new(name, parent);
		endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		data_sent = apb_transaction :: type_id :: create("data_sent");
	endfunction

	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
	endfunction

	task run_phase(uvm_phase phase);
		super.run_phase(phase);
			forever
				begin
					collect_data();
				end
	endtask

	task collect_data();
		@(m_vif.mmon_cb) // Setup Phase Sampled
			if(m_vif.mmon_cb.Psel && !m_vif.mmon_cb.Penable)
				begin
					data_sent.Pwrite = m_vif.mmon_cb.Pwrite;
					data_sent.Paddr = m_vif.mmon_cb.Paddr;
					data_sent.Pwdata = m_vif.mmon_cb.Pwdata;
					data_sent.Psel = m_vif.mmon_cb.Psel;
				end

		@(m_vif.mmon_cb) 
			wait(m_vif.mmon_cb.Penable);
			wait(m_vif.mmon_cb.Pready);
			
			data_sent.Pready = m_vif.mmon_cb.Pready;
			data_sent.Penable = m_vif.mmon_cb.Penable;

			if(!m_vif.mmon_cb.Pwrite)
				data_sent.Prdata = m_vif.mmon_cb.Prdata;
		//Screboard Logic 
	endtask
endclass 
