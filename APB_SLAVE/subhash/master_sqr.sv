class master_sqr extends uvm_sequencer#(master_tx);
  `uvm_component_utils(master_sqr)
  
  function new(string name = "master_sqr", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
endclass : master_sqr

