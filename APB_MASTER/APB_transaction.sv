class apb_master_txn extends uvm_sequence_item;

	rand bit Penable;
	rand bit Psel;
	rand bit [DATA_WIDTH - 1:0] Paddr;
	rand bit [ADDR_WIDTH - 1:0] Pwdata;
	rand bit Pwrite;
	rand bit transfer;
		 bit [DATA_WIDTH - 1:0] Prdata;
		 bit Pready;
		 bit Pslverr;
		
	`uvm_object_utils(apb_master_txn)
	
	function new(string name = "APB_master_txn", uvm_component parent);
		super.new(name, parent);
	endfunction

endclass


