class apb_base_sequence extends uvm_sequence #(apb_transaction);

  `uvm_object_utils(apb_slave_sequence)

  function new(string name = "apb_slave_sequence");
    super.new(name);
  endfunction

  virtual task body();

	  //create seq_item
	  req = apb_seq_item :: type_id :: create("req");
	  start_item(req);
	  assert(req.randomize());
	  finish_item(req);
  endtask

endclass: apb_sequence


