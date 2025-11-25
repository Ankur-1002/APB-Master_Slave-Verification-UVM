class apb_base_test extends uvm_test;
    
    `uvm_component_utils(apb_base_test)
    
    apb_env env;
    
    function new(string name = "apb_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = apb_env::type_id::create("env", this);
    endfunction
    
    function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        uvm_top.print_topology();
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        #100;
        phase.drop_objection(this);
    endtask
    
endclass

class apb_write_test extends apb_base_test;
    
    `uvm_component_utils(apb_write_test)
    
    function new(string name = "apb_write_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        apb_single_write_seq seq;
        
        phase.raise_objection(this);
        
        seq = apb_single_write_seq::type_id::create("seq");
        repeat(5) begin
            seq.start(env.agent.sequencer);
        end
        
        #100;
        phase.drop_objection(this);
    endtask
    
endclass

class apb_read_test extends apb_base_test;
    
    `uvm_component_utils(apb_read_test)
    
    function new(string name = "apb_read_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        apb_single_read_seq seq;
        
        phase.raise_objection(this);
        
        seq = apb_single_read_seq::type_id::create("seq");
      repeat(1) begin
            seq.start(env.agent.sequencer);
        end
        #100;
        phase.drop_objection(this);
    endtask
    
endclass

class apb_random_test extends apb_base_test;
    
    `uvm_component_utils(apb_random_test)
    
    function new(string name = "apb_random_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        apb_random_seq seq;
        
        phase.raise_objection(this);
        
        seq = apb_random_seq::type_id::create("seq");
        seq.start(env.agent.sequencer);
        
        #100;
        phase.drop_objection(this);
    endtask
    
endclass

class apb_err_write_test extends apb_base_test;
    
  `uvm_component_utils(apb_err_write_test)
    
  function new(string name = "apb_err_write_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        apb_single_write_err_seq seq;
        
        phase.raise_objection(this);
        
        seq = apb_single_write_err_seq::type_id::create("seq");
        seq.start(env.agent.sequencer);
        
        #100;
        phase.drop_objection(this);
    endtask
    
endclass

class apb_err_read_test extends apb_base_test;
    
  `uvm_component_utils(apb_err_read_test)
    
  function new(string name = "apb_err_write_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        apb_single_read_err_seq seq;
        
        phase.raise_objection(this);
        
        seq = apb_single_read_err_seq::type_id::create("seq");
        seq.start(env.agent.sequencer);
        
        #100;
        phase.drop_objection(this);
    endtask
    
endclass
