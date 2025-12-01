class apb_monitor extends uvm_monitor;
    
    `uvm_component_utils(apb_monitor)
    apb_master_config m_cfg;
    virtual apb_if vif;
    uvm_analysis_port #(apb_transaction) item_collected_port;
    apb_transaction trans;
   
    function new(string name = "apb_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collected_port = new("item_collected_port", this);
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
					collect_data();
				end
	endtask

	task collect_data();
		trans = apb_transaction::type_id::create("trans", this);	
		@(vif.mmon_cb)// Setup Phase Sampled
		`uvm_info(get_full_name(),"Entering into the monitor run phase", UVM_MEDIUM)
			if(vif.mmon_cb.PSELx && !vif.mmon_cb.PENABLE)
				begin
					trans.pwrite = vif.mmon_cb.PWRITE;
					trans.paddr = vif.mmon_cb.PADDR;
					trans.pwdata = vif.mmon_cb.PWDATA;
					trans.pselx = 1;
				end
		`uvm_info(get_full_name(), " Entering to the access phase", UVM_MEDIUM)
		@(vif.mmon_cb) 
			wait(vif.mmon_cb.PENABLE);
			wait(vif.mmon_cb.PREADY);
		`uvm_info(get_full_name(), " Got PREADY and PENABLE", UVM_MEDIUM)	
			trans.pready = vif.mmon_cb.PREADY;
			trans.penable = vif.mmon_cb.PENABLE;

			if(!vif.mmon_cb.PWRITE)
				trans.prdata = vif.mmon_cb.PRDATA;

		 item_collected_port.write(trans);
        `uvm_info(get_type_name(), $sformatf("Transaction Monitored:\n%s", 
                  trans.sprint()), UVM_HIGH)
       
	endtask        
endclass
