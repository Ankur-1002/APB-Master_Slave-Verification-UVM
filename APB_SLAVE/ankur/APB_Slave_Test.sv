class apb_test extends uvm_test;
  `uvm_component_utils(apb_test)
  apb_env env;
  apb_sequence sequences;
  function new(string name="apb_test",uvm_component parent);
    super.new(name,parent);
  endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env=apb_env::type_id::create("env",this);
    sequences=apb_sequence::type_id::create("sequences",this);
  endfunction
  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
    sequences.start(env.agent.sequencer);    //give the name of env and agent
    phase.drop_objection(this);
  endtask
endclass
