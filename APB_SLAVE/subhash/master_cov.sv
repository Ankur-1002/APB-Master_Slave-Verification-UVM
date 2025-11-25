class master_cov extends uvm_subscriber#(master_tx);
  `uvm_component_utils(master_cov)

  uvm_analysis_imp#(master_tx, master_cov) ap_imp;
  master_tx tx;

	virtual master_intf mvif;
	
 covergroup master_cg; 

    // ADDRESS RANGE
    PADDR_cp: coverpoint tx.PADDR {
      bins low    = {[0:50]};
      bins mid    = {[51:500]};
      bins high   = {[501:1024]};
      option.auto_bin_max = 32;
    }

    // PWDATA DISTRIBUTION
    PWDATA_cp: coverpoint tx.PWDATA {
      option.auto_bin_max = 16;
    }

    // READ / WRITE
    PWRITE_cp: coverpoint tx.PWRITE {
      bins write = {1};
      bins read  = {0};
    }

    // ODD / EVEN ADDRESS bit
    ADDR_LSB_cp: coverpoint tx.PADDR[0] {
      bins even = {0};
      bins odd  = {1};
    }

    // CROSS COVERAGE
    RW_vs_ODDEVEN: cross PWRITE_cp, ADDR_LSB_cp;
    ADDR_vs_DATA:  cross PADDR_cp, PWDATA_cp;

  endgroup


  function new(string name, uvm_component parent);
    super.new(name, parent);
    master_cg = new();
  endfunction

	virtual function void write(T t);
		$cast(tx,t);
    	master_cg.sample();
		//t.print();
	endfunction

  function void build_phase(uvm_phase phase);
    ap_imp = new("ap_imp", this);
  endfunction

endclass
