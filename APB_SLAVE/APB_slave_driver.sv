
class apb_slave_driver extends uvm_driver;
	`uvm_component_utils(apb_slave_driver)

		function new(string name = "apb_slave_driver", uvm_component parent);
			super.new(name, parent);
		endfunction

		function void build_phase(uvm_phase phase);
			super.build_phase(phase);
		endfunction

		function void connect_phase(uvm_phase phase);
			super.connect_phase(phase);
		endfunction

		task run_phase(uvm_phase phase);
			super.run_phase(phase);
		//logic
		endtask

endclass
