class master_mon extends uvm_monitor;
	`uvm_component_utils(master_mon)
	
	virtual master_intf mvif;
	uvm_analysis_port #(master_tx) monitor_port;
	
	function new(string name = "master_mon", uvm_component parent = null);
	  super.new(name, parent);
	endfunction
	
	function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  monitor_port = new("monitor_port", this);
	
	  if (!uvm_config_db#(virtual master_intf)::get(this, "", "MVIF", mvif))
	    `uvm_fatal("MASTER_MON", "Cannot get virtual interface MVIF")
	
	  //`uvm_info("MASTER_MON","Monitor build complete",UVM_LOW)
	endfunction
	
/*	
	task run_phase(uvm_phase phase);
		master_tx tx;

		`uvm_info("MASTER_MON","Monitor run_phase started",UVM_LOW);

		forever begin
    		@(mvif.mmon_cb);
			if (mvif.PSELx && mvif.PENABLE) begin
			    tx = master_tx::type_id::create("tx", this);
			    tx.PWRITE = mvif.PWRITE;
			    tx.PADDR  = mvif.PADDR;
			    tx.PSELx  = mvif.PSELx;
			    tx.PENABLE = mvif.PENABLE;
			
			    if (mvif.PWRITE)
			        tx.PWDATA = mvif.PWDATA;
			    else
			        tx.PRDATA = mvif.PRDATA;
			
			    monitor_port.write(tx);
			end

			//wait(mvif.mmon_cb.PSELx && mvif.mmon_cb.PENABLE &&  mvif.mmon_cb.PREADY) 

        	////`uvm_info("MASTER_MON","VALID APB TRANSFER DETECTED",UVM_LOW);

        	//tx = master_tx::type_id::create("tx", this);

        	//tx.PWRITE  = mvif.mmon_cb.PWRITE;
        	//tx.PADDR   = mvif.mmon_cb.PADDR;
        	//tx.PENABLE = mvif.mmon_cb.PENABLE;
        	//tx.PSELx   = mvif.mmon_cb.PSELx;

        	//if (tx.PWRITE)
        	//  tx.PWDATA = mvif.mmon_cb.PWDATA;
        	//else
        	//  tx.PRDATA = mvif.mmon_cb.PRDATA;

        	//monitor_port.write(tx);
        	//tx.print();
	    end
	endtask
*/
task run_phase(uvm_phase phase);
  master_tx tx;
  `uvm_info("MASTER_MON","Monitor run_phase started",UVM_LOW);

  forever begin
    // sample on DUT clock
    @(posedge mvif.PCLK);

    // debug snapshot every cycle (helps see signal activity)
    //`uvm_info("MASTER_MON_DBG",$sformatf("CLK: PSELx=%0b PENABLE=%0b PREADY=%0b PWRITE=%0b ADDR=%0h PWDATA=%0h PRDATA=%0h",mvif.PSELx, mvif.PENABLE, mvif.PREADY,mvif.PWRITE, mvif.PADDR, mvif.PWDATA, mvif.PRDATA), UVM_LOW);

    // When an APB transfer is valid on this sample (sample at the expected point)
    if (mvif.PSELx && mvif.PENABLE) begin
      tx = master_tx::type_id::create("tx", this);
      tx.PWRITE  = mvif.PWRITE;
      tx.PADDR   = mvif.PADDR;
      tx.PENABLE = mvif.PENABLE;
      tx.PSELx   = mvif.PSELx;

      // capture read/write data as available on this cycle
      if (tx.PWRITE) begin
        tx.PWDATA = mvif.PWDATA;
      end else begin
        tx.PRDATA = mvif.PRDATA;
      end

      // record PREADY too (optional field in tx)
      // tx.PREADY = mvif.PREADY; // if your transaction has PREADY field

      // debug before write
      //`uvm_info("MON_DEBUG", $sformatf("Monitor writing tx: PWRITE=%0b ADDR=%0h", tx.PWRITE, tx.PADDR), UVM_MEDIUM);

      monitor_port.write(tx);
    end
  end
endtask

endclass 

