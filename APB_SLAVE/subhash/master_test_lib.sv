class master_base_test extends uvm_test;
	`uvm_component_utils(master_base_test)
	master_env env;

  function new(string name="master_base_test",uvm_component parent);
		super.new(name,parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		`uvm_info("MASTER_BASE_TEST","build_phase of master_base_test",UVM_NONE)
		env = master_env::type_id::create("env",this);
	endfunction

	task run_phase(uvm_phase phase);
		master_base_seq seq;
		`uvm_info("MASTER_BASE_TEST","run_phase of master_base_test",UVM_NONE)
		
      	seq = master_base_seq::type_id::create("seq");
		phase.raise_objection(this);
      	seq.start(env.m_agnt.m_sqr);
		phase.phase_done.set_drain_time(this,100);
		phase.drop_objection(this);
	endtask

	function void end_of_elaboration_phase(uvm_phase phase);
		uvm_top.print_topology();
	endfunction
	
endclass


class first_test extends master_base_test;
	`uvm_component_utils(first_test)

   first_seq seq;

	function new(string name="first_test",uvm_component parent);
		super.new(name,parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
	endfunction

    task run_phase(uvm_phase phase);
      `uvm_info("FIRST_TEST","run_phase - starting first_seq",UVM_NONE)

      phase.raise_objection(this);

      seq = first_seq::type_id::create("seq");
      seq.start(env.m_agnt.m_sqr);

      #100;
      phase.drop_objection(this);
    endtask


endclass


class odd_test extends master_base_test;
	`uvm_component_utils(odd_test)

   	odd_seqs seq;

	function new(string name="odd_test",uvm_component parent);
		super.new(name,parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
	endfunction

	task run_phase(uvm_phase phase);
	//	$display("I AM IN TEST1");
		phase.raise_objection(this);
	//	$display("I AM IN TEST XX");
		seq = odd_seqs::type_id::create("seq");
	//	$display("I AM IN TEST YY");
        seq.start(env.m_agnt.m_sqr);
	    phase.phase_done.set_drain_time(this,100);
		phase.drop_objection(this);

	endtask
endclass

class even_test extends master_base_test;
	`uvm_component_utils(even_test)

   	even_seqs seq;

	function new(string name="even_test",uvm_component parent);
		super.new(name,parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
	endfunction

	task run_phase(uvm_phase phase);
		super.run_phase(phase);
	
		phase.raise_objection(this);
		
      	seq = even_seqs::type_id::create("seq");
      	seq.start(env.m_agnt.m_sqr);
		phase.phase_done.set_drain_time(this,100);
		phase.drop_objection(this);

	endtask
endclass


class incr_addr_test extends master_base_test;
	`uvm_component_utils(incr_addr_test)

   incr_addr_seqs seq;

	function new(string name="incr_addr_test",uvm_component parent);
		super.new(name,parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
	endfunction

	task run_phase(uvm_phase phase);
		super.run_phase(phase);
	
		phase.raise_objection(this);
		
      	seq = incr_addr_seqs::type_id::create("seq");
      	seq.start(env.m_agnt.m_sqr);
		phase.phase_done.set_drain_time(this,100);
		phase.drop_objection(this);

	endtask
endclass

class decr_addr_test extends master_base_test;
	`uvm_component_utils(decr_addr_test)

   decr_addr_seqs seq;

	function new(string name="decr_addr_test",uvm_component parent);
		super.new(name,parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
	endfunction

	task run_phase(uvm_phase phase);
		super.run_phase(phase);
	
		phase.raise_objection(this);
		
        seq = decr_addr_seqs::type_id::create("seq");
        seq.start(env.m_agnt.m_sqr);
		phase.phase_done.set_drain_time(this,100);
		phase.drop_objection(this);

	endtask
endclass

class incr_data_test extends master_base_test;
	`uvm_component_utils(incr_data_test)

   	incr_data_seqs seq;

	function new(string name="rand_test",uvm_component parent);
		super.new(name,parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
	endfunction

	task run_phase(uvm_phase phase);
		super.run_phase(phase);
	
		phase.raise_objection(this);
		
        seq = incr_data_seqs::type_id::create("seq");
        seq.start(env.m_agnt.m_sqr);
		phase.phase_done.set_drain_time(this,100);
		phase.drop_objection(this);

	endtask
endclass


class decr_data_test extends master_base_test;
	`uvm_component_utils(decr_data_test)

   	decr_data_seqs seq;

	function new(string name="rand_test",uvm_component parent);
		super.new(name,parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
	endfunction

	task run_phase(uvm_phase phase);
		super.run_phase(phase);
	
		phase.raise_objection(this);
		
        seq = decr_data_seqs::type_id::create("seq");
        seq.start(env.m_agnt.m_sqr);
        phase.phase_done.set_drain_time(this,100);
		phase.drop_objection(this);

	endtask
endclass


class rand_test extends master_base_test;
	`uvm_component_utils(rand_test)

   rand_seqs seq;

	function new(string name="rand_test",uvm_component parent);
		super.new(name,parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
	endfunction

	task run_phase(uvm_phase phase);
		super.run_phase(phase);
	
		phase.raise_objection(this);
		
      	seq = rand_seqs::type_id::create("seq");
      	seq.start(env.m_agnt.m_sqr);
		phase.phase_done.set_drain_time(this,100);
		phase.drop_objection(this);

	endtask
endclass

