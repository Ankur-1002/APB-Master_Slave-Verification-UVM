class apb_master_sequence extends uvm_sequence #(apb_transaction);

  `uvm_object_utils(apb_master_sequence)

  function new(string name = "apb_master_sequence");
    super.new(name);
  endfunction

  task body;
  // How to print the data in what format
  endtask

endclass
