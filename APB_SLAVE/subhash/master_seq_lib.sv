class master_base_seq extends uvm_sequence#(master_tx);
  `uvm_object_utils(master_base_seq)
	
  function new(string name="master_base_seq");
		super.new(name);
	endfunction

	task pre_body;
		`uvm_info("master_seq_lib","pre_body",UVM_NONE);
	endtask
	
  	task body();
      `uvm_info("master_seq_lib","body",UVM_NONE);
    endtask
  
	task post_body();
		`uvm_info("master_seq_lib","post_body",UVM_NONE);
	endtask

endclass


class first_seq extends master_base_seq;

	`uvm_object_utils(first_seq)


	int store[$];
	int temp;
	int i;

	function new(string name="first_seq");
		super.new(name);
	endfunction 

	task body();	
      	for(i=0;i<=20;i++) begin
          req = master_tx::type_id::create("req");
          start_item(req);
          assert(req.randomize()with {PWRITE==1;PSELx==1;})
          store.push_back(req.PADDR);
          finish_item(req);
          $display("i=%0d---%0d",i,req.PADDR);	
		end
		
      	for(i=0;i<=20;i++) begin
          req = master_tx::type_id::create("req");
          start_item(req);
          assert(req.randomize()with {PWRITE==0;PSELx==1;PADDR==temp;})
          finish_item(req);
          temp = store.pop_front();
          $display("i=%0d---%0d",i,temp);
		end
    endtask

endclass



class odd_seqs extends master_base_seq;

	`uvm_object_utils(odd_seqs)

	int addrw_seq,addrr_seq;
	
	function new(string name="odd_seqs");
		super.new(name);
	endfunction

	task body();
      	repeat(100) begin
          req=master_tx::type_id::create("req");
          start_item(req);
          assert(req.randomize()with{PWRITE==1;PADDR==(2*addrw_seq+1);PSELx==1;})
          finish_item(req);
          addrw_seq++;
		end

      	repeat(100) begin
			req=master_tx::type_id::create("req");
			start_item(req);
          assert(req.randomize()with{PWRITE==0;PADDR==(2*addrr_seq+1);PSELx==1;})
			finish_item(req);
			addrr_seq++;
		end

	endtask

endclass

class even_seqs extends master_base_seq;

	`uvm_object_utils(even_seqs)

	int addrw_seq, addrr_seq;
	
	function new(string name="even_seqs");
		super.new(name);
	endfunction

	task body();
      	repeat(100) begin
          req = master_tx::type_id::create("req");
          start_item(req);
          assert(req.randomize()with{PWRITE==1;PADDR==(2*addrw_seq);PSELx==1;})
          finish_item(req);
          addrw_seq++;
		end

      	repeat(100) begin
			req=master_tx::type_id::create("req");
			start_item(req);
          assert(req.randomize() with {PWRITE==0;PADDR==(2*addrr_seq);PSELx==1;})
			finish_item(req);
			addrr_seq++;
		end

	endtask

endclass

class incr_addr_seqs extends master_base_seq;
	`uvm_object_utils(incr_addr_seqs)

	function new(string name="incr_addr_seqs");
		super.new(name);
	endfunction
  
    int i;
    int store[$];
    int temp;

  	task body();
      	for(i=0;i<=50;i++) begin
          req = master_tx::type_id::create("req");
          start_item(req);
          assert(req.randomize()with{PADDR==temp;PWRITE==1;PSELx==1;})
          temp = temp+20;
          store.push_back(temp);
          finish_item(req);
		end
      
      	for(i=0;i<=50;i++) begin
          req = master_tx::type_id::create("req");
          start_item(req);
          assert(req.randomize()with{PWRITE==0;PADDR==temp;PSELx==1;})
          temp = store.pop_front();
          finish_item(req);
		end

	endtask

endclass

class decr_addr_seqs extends master_base_seq;

	`uvm_object_utils(decr_addr_seqs)

	function new(string name="decr_addr_seqs");
		super.new(name);
	endfunction
  
    int i;
    int store[$];
    int temp = 20;
  
	task body();
      	for(i=0;i<=20;i++) begin
          req = master_tx::type_id::create("req");
          start_item(req);
          assert(req.randomize()with{PADDR==temp;PWRITE==1;PSELx==1;})
          temp = temp-1;
          store.push_back(temp);
          finish_item(req);
		end
      	
      	for(i=0;i<=20;i++) begin
          req = master_tx::type_id::create("req");
          start_item(req);
          temp = store.pop_front();
          assert(req.randomize()with{PWRITE==0;PADDR==temp;PSELx==1;})
          finish_item(req);
		end

	endtask

endclass

class incr_data_seqs extends master_base_seq;
	`uvm_object_utils(incr_data_seqs)

	function new(string name="incr_data_seqs");
		super.new(name);
	endfunction
  
    int i;
    int store[$];
    int temp;
  
	task body();
      	for(i=0;i<=50;i++) begin
          req=master_tx::type_id::create("req");
          start_item(req);
          assert(req.randomize()with{PADDR==temp*2;PWDATA==temp;PWRITE==1;PSELx==1;})
          temp = temp+1;
          store.push_back(temp);
          finish_item(req);
		end
      	for(i=0;i<=50;i++) begin
          req = master_tx::type_id::create("req");
          start_item(req);
          assert(req.randomize()with{PWRITE==0;PADDR==temp*2;PSELx==1;})
          temp=store.pop_front();
          finish_item(req);
		end

	endtask

endclass

class decr_data_seqs extends master_base_seq;

	`uvm_object_utils(decr_data_seqs)

	function new(string name="decr_data_seqs");
		super.new(name);
	endfunction
  
    int i;
    int store[$];
    int temp=50;
  
	task body();
      	for(i=0;i<=50;i++) begin
          req = master_tx::type_id::create("req");
          start_item(req);
          assert(req.randomize() with {PADDR==temp*2;PWDATA==temp;PWRITE==1;PSELx==1;})
          temp = temp-1;
          store.push_back(temp);
          finish_item(req);
		end
      	for(i=0;i<=50;i++) begin
          req = master_tx::type_id::create("req");
          start_item(req);
          temp = store.pop_front();
          assert(req.randomize() with {PWRITE==0;PADDR==temp*2;PSELx==1;})
          finish_item(req);
		end

	endtask

endclass

class rand_seqs extends master_base_seq;
	`uvm_object_utils(rand_seqs)
	
	function new(string name="rand_seqs");
		super.new(name);
	endfunction

	task body();
      	repeat(100) begin
          req=master_tx::type_id::create("req");
          start_item(req);
          assert(req.randomize()with{PADDR inside{[100:500]};PWRITE==1;PSELx==1;})
          finish_item(req);
		end
		repeat(100)begin
          req=master_tx::type_id::create("req");
          start_item(req);
          assert(req.randomize()with{PWRITE==0;PADDR inside{[100:500]};PSELx==1;})
          finish_item(req);
		end

	endtask
	
endclass