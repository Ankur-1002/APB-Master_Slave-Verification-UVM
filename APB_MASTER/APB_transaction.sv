class apb_transaction extends uvm_sequence_item;

	rand bit Penable;
	rand bit Psel;
	rand bit [DATA_WIDTH - 1:0] Paddr;
	rand bit [ADDR_WIDTH - 1:0] Pwdata;
	rand bit Pwrite;
	rand bit [DATA_WIDTH - 1:0] Prdata;
	rand bit Pready;
	rand bit Pslverr;
		
	`uvm_object_utils(apb_transaction)
	
	function new(string name = "APB_transaction", uvm_component parent);
		super.new(name, parent);
	endfunction

endclass


