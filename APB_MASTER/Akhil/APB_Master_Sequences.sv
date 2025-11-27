// Base Sequence
class apb_base_sequence extends uvm_sequence #(apb_transaction);
    
    `uvm_object_utils(apb_base_sequence)
    
    function new(string name = "apb_base_sequence");
        super.new(name);
    endfunction
    
endclass

Single_write_Sequence:-
class apb_write_single_seq extends apb_base_sequence;

	`uvm_object_utils(apb_write_single_seq)

function new(string name = "apb_write_single_seq");
	super.new(name);
endfunction

task body();
apb_transaction trans;
trans = apb_transaction::type_id::create("trans");

start_item(trans);
assert(trans.randomize() with {write_read == 1;
			       write_paddr inside {[0:255]};});
finish_item(trans);
endtask

endclass

Single_read_sequence:-
class  apb_read_single_seq extends apb_base_sequence;

	`uvm_object_utils(apb_read_single_seq)

function new(string name = "apb_read_single_seq");
	super.new(name);
endfunction

task body();
apb_transaction trans;
trans = apb_transaction::type_id::create("trans");

start_item(trans);
assert(trans.randomize() with {write_read == 0;
			       read_paddr inside {[0:255]};});
finish_item(trans);
endtask
endclass

Mixed_write_read_sequence:-
class apb_write_read_seq extends apb_sequence;;
  `uvm_object_utils(apb_write_read_seq)
 
  int unsigned num_trans = 10;
  rand bit[31:0]addr_q[$];//queue to store write paddr
 
  function new(string name = "apb_write_read_seq");
    super.new(name);
  endfunction
 
  task body();
    apb_transaction trans;
    trans = apb_transction::type_id::create("trans");
    for (int i = 0; i < num_trans; i++) begin
      start_item(trans);
      assert(trans.randomize() with {write_read == 1;
                                   write_paddr inside{[0:255]};
                                   });
            
      finish_item(trans);
        //push the write paddr into queue
      addr_q.push_back(trans.write_paddr);

     `uvm_info("WRITE", $sformatf("WRITE[%0d]: write_data=0x%0h|write_paddr=0x%0h|", i, trans.write_data,trans.write_paddr), UVM_LOW)
    end
 
  //read from the written address
   for (int i = 0; i < num_trans; i++) begin
      start_item(trans);
 
      assert(trans.randomize() with {write_read == 0;
                                   read_paddr == addr_q[i];
	 			   write_data == 0;
                                  });
      finish_item(trans);
      `uvm_info("READ", $sformatf("READ[%0d]:read_paddr=0x%0h", i, xtn.read_paddr),UVM_LOW)
     end
  endtask
endclass
 

